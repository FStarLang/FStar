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
         (let repr =
            let r =
              (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.pos
               in
            let uu____526 =
              check_and_gen "repr" Prims.int_one ed.FStar_Syntax_Syntax.repr
               in
            match uu____526 with
            | (repr_us,repr_t,repr_ty) ->
                ((let uu____551 =
                    FStar_All.pipe_right quals
                      (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)
                     in
                  if uu____551
                  then
                    let repr_t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.UnfoldUntil
                           (FStar_Syntax_Syntax.Delta_constant_at_level
                              Prims.int_zero);
                        FStar_TypeChecker_Env.AllowUnboundUniverses] env0
                        repr_t
                       in
                    let uu____559 =
                      let uu____560 = FStar_Syntax_Subst.compress repr_t1  in
                      uu____560.FStar_Syntax_Syntax.n  in
                    match uu____559 with
                    | FStar_Syntax_Syntax.Tm_abs (uu____563,t,uu____565) ->
                        let uu____590 =
                          let uu____591 = FStar_Syntax_Subst.compress t  in
                          uu____591.FStar_Syntax_Syntax.n  in
                        (match uu____590 with
                         | FStar_Syntax_Syntax.Tm_arrow (uu____594,c) ->
                             let uu____616 =
                               let uu____618 =
                                 let uu____620 =
                                   FStar_All.pipe_right c
                                     FStar_Syntax_Util.comp_effect_name
                                    in
                                 FStar_All.pipe_right uu____620
                                   (FStar_TypeChecker_Env.is_total_effect
                                      env0)
                                  in
                               Prims.op_Negation uu____618  in
                             if uu____616
                             then
                               let uu____625 =
                                 let uu____631 =
                                   let uu____633 =
                                     FStar_All.pipe_right
                                       ed.FStar_Syntax_Syntax.mname
                                       FStar_Ident.string_of_lid
                                      in
                                   FStar_Util.format1
                                     "Effect %s is marked total but its underlying effect is not"
                                     uu____633
                                    in
                                 (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                                   uu____631)
                                  in
                               FStar_Errors.raise_error uu____625 r
                             else ()
                         | uu____640 ->
                             let uu____641 =
                               let uu____647 =
                                 let uu____649 =
                                   FStar_All.pipe_right
                                     ed.FStar_Syntax_Syntax.mname
                                     FStar_Ident.string_of_lid
                                    in
                                 let uu____652 =
                                   FStar_Syntax_Print.term_to_string t  in
                                 FStar_Util.format2
                                   "repr body for %s is not an arrow (%s)"
                                   uu____649 uu____652
                                  in
                               (FStar_Errors.Fatal_UnexpectedEffect,
                                 uu____647)
                                in
                             FStar_Errors.raise_error uu____641 r)
                    | uu____656 ->
                        let uu____657 =
                          let uu____663 =
                            let uu____665 =
                              FStar_All.pipe_right
                                ed.FStar_Syntax_Syntax.mname
                                FStar_Ident.string_of_lid
                               in
                            let uu____668 =
                              FStar_Syntax_Print.term_to_string repr_t1  in
                            FStar_Util.format2
                              "repr for %s is not an abstraction (%s)"
                              uu____665 uu____668
                             in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____663)
                           in
                        FStar_Errors.raise_error uu____657 r
                  else ());
                 (let uu____674 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
                  match uu____674 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____694 = fresh_a_and_u_a "a"  in
                      (match uu____694 with
                       | (a,u) ->
                           let rest_bs =
                             let signature_ts =
                               let uu____716 = signature  in
                               match uu____716 with
                               | (us1,t,uu____731) -> (us1, t)  in
                             let uu____748 =
                               let uu____749 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____749
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               signature_ts u uu____748
                              in
                           let bs = a :: rest_bs  in
                           let k =
                             let uu____776 =
                               let uu____779 = FStar_Syntax_Util.type_u ()
                                  in
                               FStar_All.pipe_right uu____779
                                 (fun uu____792  ->
                                    match uu____792 with
                                    | (t,u1) ->
                                        let uu____799 =
                                          let uu____802 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____802
                                           in
                                        FStar_Syntax_Syntax.mk_Total' t
                                          uu____799)
                                in
                             FStar_Syntax_Util.arrow bs uu____776  in
                           let g = FStar_TypeChecker_Rel.teq env ty k  in
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (let uu____805 =
                               let uu____808 =
                                 FStar_All.pipe_right k
                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                      env)
                                  in
                               FStar_Syntax_Subst.close_univ_vars us
                                 uu____808
                                in
                             (repr_us, repr_t, uu____805))))))
             in
          log_combinator "repr" repr;
          (let fresh_repr r env u a_tm =
             let signature_ts =
               let uu____843 = signature  in
               match uu____843 with | (us,t,uu____858) -> (us, t)  in
             let repr_ts =
               let uu____876 = repr  in
               match uu____876 with | (us,t,uu____891) -> (us, t)  in
             FStar_TypeChecker_Util.fresh_effect_repr env r
               ed.FStar_Syntax_Syntax.mname signature_ts repr_ts u a_tm
              in
           let not_an_arrow_error comb n1 t r =
             let uu____941 =
               let uu____947 =
                 let uu____949 = FStar_Util.string_of_int n1  in
                 let uu____951 = FStar_Syntax_Print.tag_of_term t  in
                 let uu____953 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format5
                   "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str comb
                   uu____949 uu____951 uu____953
                  in
               (FStar_Errors.Fatal_UnexpectedEffect, uu____947)  in
             FStar_Errors.raise_error uu____941 r  in
           let return_repr =
             let r =
               (FStar_Pervasives_Native.snd
                  ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                in
             let uu____983 =
               check_and_gen "return_repr" Prims.int_one
                 ed.FStar_Syntax_Syntax.return_repr
                in
             match uu____983 with
             | (ret_us,ret_t,ret_ty) ->
                 let uu____1007 =
                   FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                 (match uu____1007 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____1027 = fresh_a_and_u_a "a"  in
                      (match uu____1027 with
                       | (a,u_a) ->
                           let rest_bs =
                             let uu____1056 =
                               let uu____1057 =
                                 FStar_Syntax_Subst.compress ty  in
                               uu____1057.FStar_Syntax_Syntax.n  in
                             match uu____1056 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1069)
                                 when
                                 (FStar_List.length bs) >= (Prims.of_int (2))
                                 ->
                                 let uu____1097 =
                                   FStar_Syntax_Subst.open_binders bs  in
                                 (match uu____1097 with
                                  | (a',uu____1107)::bs1 ->
                                      let uu____1127 =
                                        let uu____1128 =
                                          FStar_All.pipe_right bs1
                                            (FStar_List.splitAt
                                               ((FStar_List.length bs1) -
                                                  Prims.int_one))
                                           in
                                        FStar_All.pipe_right uu____1128
                                          FStar_Pervasives_Native.fst
                                         in
                                      let uu____1194 =
                                        let uu____1207 =
                                          let uu____1210 =
                                            let uu____1211 =
                                              let uu____1218 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  (FStar_Pervasives_Native.fst
                                                     a)
                                                 in
                                              (a', uu____1218)  in
                                            FStar_Syntax_Syntax.NT uu____1211
                                             in
                                          [uu____1210]  in
                                        FStar_Syntax_Subst.subst_binders
                                          uu____1207
                                         in
                                      FStar_All.pipe_right uu____1127
                                        uu____1194)
                             | uu____1233 ->
                                 not_an_arrow_error "return"
                                   (Prims.of_int (2)) ty r
                              in
                           let bs =
                             let uu____1245 =
                               let uu____1254 =
                                 let uu____1263 = fresh_x_a "x" a  in
                                 [uu____1263]  in
                               FStar_List.append rest_bs uu____1254  in
                             a :: uu____1245  in
                           let uu____1295 =
                             let uu____1300 =
                               FStar_TypeChecker_Env.push_binders env bs  in
                             let uu____1301 =
                               FStar_All.pipe_right
                                 (FStar_Pervasives_Native.fst a)
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             fresh_repr r uu____1300 u_a uu____1301  in
                           (match uu____1295 with
                            | (repr1,g) ->
                                let k =
                                  let uu____1321 =
                                    FStar_Syntax_Syntax.mk_Total' repr1
                                      (FStar_Pervasives_Native.Some u_a)
                                     in
                                  FStar_Syntax_Util.arrow bs uu____1321  in
                                let g_eq = FStar_TypeChecker_Rel.teq env ty k
                                   in
                                ((let uu____1326 =
                                    FStar_TypeChecker_Env.conj_guard g g_eq
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env uu____1326);
                                 (let uu____1327 =
                                    let uu____1330 =
                                      FStar_All.pipe_right k
                                        (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                           env)
                                       in
                                    FStar_Syntax_Subst.close_univ_vars us
                                      uu____1330
                                     in
                                  (ret_us, ret_t, uu____1327))))))
              in
           log_combinator "return_repr" return_repr;
           (let bind_repr =
              let r =
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                 in
              let uu____1357 =
                check_and_gen "bind_repr" (Prims.of_int (2))
                  ed.FStar_Syntax_Syntax.bind_repr
                 in
              match uu____1357 with
              | (bind_us,bind_t,bind_ty) ->
                  let uu____1381 =
                    FStar_Syntax_Subst.open_univ_vars bind_us bind_ty  in
                  (match uu____1381 with
                   | (us,ty) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                          in
                       let uu____1401 = fresh_a_and_u_a "a"  in
                       (match uu____1401 with
                        | (a,u_a) ->
                            let uu____1421 = fresh_a_and_u_a "b"  in
                            (match uu____1421 with
                             | (b,u_b) ->
                                 let rest_bs =
                                   let uu____1450 =
                                     let uu____1451 =
                                       FStar_Syntax_Subst.compress ty  in
                                     uu____1451.FStar_Syntax_Syntax.n  in
                                   match uu____1450 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs,uu____1463) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (4))
                                       ->
                                       let uu____1491 =
                                         FStar_Syntax_Subst.open_binders bs
                                          in
                                       (match uu____1491 with
                                        | (a',uu____1501)::(b',uu____1503)::bs1
                                            ->
                                            let uu____1533 =
                                              let uu____1534 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - (Prims.of_int (2))))
                                                 in
                                              FStar_All.pipe_right uu____1534
                                                FStar_Pervasives_Native.fst
                                               in
                                            let uu____1632 =
                                              let uu____1645 =
                                                let uu____1648 =
                                                  let uu____1649 =
                                                    let uu____1656 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           a)
                                                       in
                                                    (a', uu____1656)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____1649
                                                   in
                                                let uu____1663 =
                                                  let uu____1666 =
                                                    let uu____1667 =
                                                      let uu____1674 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             b)
                                                         in
                                                      (b', uu____1674)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____1667
                                                     in
                                                  [uu____1666]  in
                                                uu____1648 :: uu____1663  in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____1645
                                               in
                                            FStar_All.pipe_right uu____1533
                                              uu____1632)
                                   | uu____1689 ->
                                       not_an_arrow_error "bind"
                                         (Prims.of_int (4)) ty r
                                    in
                                 let bs = a :: b :: rest_bs  in
                                 let uu____1713 =
                                   let uu____1724 =
                                     let uu____1729 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs
                                        in
                                     let uu____1730 =
                                       FStar_All.pipe_right
                                         (FStar_Pervasives_Native.fst a)
                                         FStar_Syntax_Syntax.bv_to_name
                                        in
                                     fresh_repr r uu____1729 u_a uu____1730
                                      in
                                   match uu____1724 with
                                   | (repr1,g) ->
                                       let uu____1745 =
                                         let uu____1752 =
                                           FStar_Syntax_Syntax.gen_bv "f"
                                             FStar_Pervasives_Native.None
                                             repr1
                                            in
                                         FStar_All.pipe_right uu____1752
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       (uu____1745, g)
                                    in
                                 (match uu____1713 with
                                  | (f,guard_f) ->
                                      let uu____1792 =
                                        let x_a = fresh_x_a "x" a  in
                                        let uu____1805 =
                                          let uu____1810 =
                                            FStar_TypeChecker_Env.push_binders
                                              env
                                              (FStar_List.append bs [x_a])
                                             in
                                          let uu____1829 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst b)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____1810 u_b
                                            uu____1829
                                           in
                                        match uu____1805 with
                                        | (repr1,g) ->
                                            let uu____1844 =
                                              let uu____1851 =
                                                let uu____1852 =
                                                  let uu____1853 =
                                                    let uu____1856 =
                                                      let uu____1859 =
                                                        FStar_TypeChecker_Env.new_u_univ
                                                          ()
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____1859
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      repr1 uu____1856
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    [x_a] uu____1853
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "g"
                                                  FStar_Pervasives_Native.None
                                                  uu____1852
                                                 in
                                              FStar_All.pipe_right uu____1851
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            (uu____1844, g)
                                         in
                                      (match uu____1792 with
                                       | (g,guard_g) ->
                                           let uu____1911 =
                                             let uu____1916 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs
                                                in
                                             let uu____1917 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.fst
                                                    b)
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             fresh_repr r uu____1916 u_b
                                               uu____1917
                                              in
                                           (match uu____1911 with
                                            | (repr1,guard_repr) ->
                                                let k =
                                                  let uu____1937 =
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      repr1
                                                      (FStar_Pervasives_Native.Some
                                                         u_b)
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    (FStar_List.append bs
                                                       [f; g]) uu____1937
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
                                                 (let uu____1966 =
                                                    let uu____1969 =
                                                      FStar_All.pipe_right k
                                                        (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                           env)
                                                       in
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      bind_us uu____1969
                                                     in
                                                  (bind_us, bind_t,
                                                    uu____1966)))))))))
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
               let uu____2003 =
                 check_and_gen "stronger_repr" Prims.int_one stronger_repr
                  in
               match uu____2003 with
               | (stronger_us,stronger_t,stronger_ty) ->
                   ((let uu____2028 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                         (FStar_Options.Other "LayeredEffects")
                        in
                     if uu____2028
                     then
                       let uu____2033 =
                         FStar_Syntax_Print.tscheme_to_string
                           (stronger_us, stronger_t)
                          in
                       let uu____2039 =
                         FStar_Syntax_Print.tscheme_to_string
                           (stronger_us, stronger_ty)
                          in
                       FStar_Util.print2
                         "stronger combinator typechecked with term: %s and type: %s\n"
                         uu____2033 uu____2039
                     else ());
                    (let uu____2048 =
                       FStar_Syntax_Subst.open_univ_vars stronger_us
                         stronger_ty
                        in
                     match uu____2048 with
                     | (us,ty) ->
                         let env =
                           FStar_TypeChecker_Env.push_univ_vars env0 us  in
                         let uu____2068 = fresh_a_and_u_a "a"  in
                         (match uu____2068 with
                          | (a,u) ->
                              let rest_bs =
                                let uu____2097 =
                                  let uu____2098 =
                                    FStar_Syntax_Subst.compress ty  in
                                  uu____2098.FStar_Syntax_Syntax.n  in
                                match uu____2097 with
                                | FStar_Syntax_Syntax.Tm_arrow
                                    (bs,uu____2110) when
                                    (FStar_List.length bs) >=
                                      (Prims.of_int (2))
                                    ->
                                    let uu____2138 =
                                      FStar_Syntax_Subst.open_binders bs  in
                                    (match uu____2138 with
                                     | (a',uu____2148)::bs1 ->
                                         let uu____2168 =
                                           let uu____2169 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     Prims.int_one))
                                              in
                                           FStar_All.pipe_right uu____2169
                                             FStar_Pervasives_Native.fst
                                            in
                                         let uu____2267 =
                                           let uu____2280 =
                                             let uu____2283 =
                                               let uu____2284 =
                                                 let uu____2291 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     (FStar_Pervasives_Native.fst
                                                        a)
                                                    in
                                                 (a', uu____2291)  in
                                               FStar_Syntax_Syntax.NT
                                                 uu____2284
                                                in
                                             [uu____2283]  in
                                           FStar_Syntax_Subst.subst_binders
                                             uu____2280
                                            in
                                         FStar_All.pipe_right uu____2168
                                           uu____2267)
                                | uu____2306 ->
                                    not_an_arrow_error "stronger"
                                      (Prims.of_int (2)) ty r
                                 in
                              let bs = a :: rest_bs  in
                              let uu____2324 =
                                let uu____2335 =
                                  let uu____2340 =
                                    FStar_TypeChecker_Env.push_binders env bs
                                     in
                                  let uu____2341 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst a)
                                      FStar_Syntax_Syntax.bv_to_name
                                     in
                                  fresh_repr r uu____2340 u uu____2341  in
                                match uu____2335 with
                                | (repr1,g) ->
                                    let uu____2356 =
                                      let uu____2363 =
                                        FStar_Syntax_Syntax.gen_bv "f"
                                          FStar_Pervasives_Native.None repr1
                                         in
                                      FStar_All.pipe_right uu____2363
                                        FStar_Syntax_Syntax.mk_binder
                                       in
                                    (uu____2356, g)
                                 in
                              (match uu____2324 with
                               | (f,guard_f) ->
                                   let uu____2403 =
                                     let uu____2408 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs
                                        in
                                     let uu____2409 =
                                       FStar_All.pipe_right
                                         (FStar_Pervasives_Native.fst a)
                                         FStar_Syntax_Syntax.bv_to_name
                                        in
                                     fresh_repr r uu____2408 u uu____2409  in
                                   (match uu____2403 with
                                    | (ret_t,guard_ret_t) ->
                                        let pure_wp_t =
                                          let pure_wp_ts =
                                            let uu____2428 =
                                              FStar_TypeChecker_Env.lookup_definition
                                                [FStar_TypeChecker_Env.NoDelta]
                                                env
                                                FStar_Parser_Const.pure_wp_lid
                                               in
                                            FStar_All.pipe_right uu____2428
                                              FStar_Util.must
                                             in
                                          let uu____2445 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              pure_wp_ts
                                             in
                                          match uu____2445 with
                                          | (uu____2450,pure_wp_t) ->
                                              let uu____2452 =
                                                let uu____2457 =
                                                  let uu____2458 =
                                                    FStar_All.pipe_right
                                                      ret_t
                                                      FStar_Syntax_Syntax.as_arg
                                                     in
                                                  [uu____2458]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  pure_wp_t uu____2457
                                                 in
                                              uu____2452
                                                FStar_Pervasives_Native.None
                                                r
                                           in
                                        let uu____2491 =
                                          let reason =
                                            FStar_Util.format1
                                              "implicit for pure_wp in checking stronger for %s"
                                              (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                             in
                                          let uu____2507 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          FStar_TypeChecker_Util.new_implicit_var
                                            reason r uu____2507 pure_wp_t
                                           in
                                        (match uu____2491 with
                                         | (pure_wp_uvar,uu____2521,guard_wp)
                                             ->
                                             let c =
                                               let uu____2536 =
                                                 let uu____2537 =
                                                   let uu____2538 =
                                                     FStar_TypeChecker_Env.new_u_univ
                                                       ()
                                                      in
                                                   [uu____2538]  in
                                                 let uu____2539 =
                                                   let uu____2550 =
                                                     FStar_All.pipe_right
                                                       pure_wp_uvar
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____2550]  in
                                                 {
                                                   FStar_Syntax_Syntax.comp_univs
                                                     = uu____2537;
                                                   FStar_Syntax_Syntax.effect_name
                                                     =
                                                     FStar_Parser_Const.effect_PURE_lid;
                                                   FStar_Syntax_Syntax.result_typ
                                                     = ret_t;
                                                   FStar_Syntax_Syntax.effect_args
                                                     = uu____2539;
                                                   FStar_Syntax_Syntax.flags
                                                     = []
                                                 }  in
                                               FStar_Syntax_Syntax.mk_Comp
                                                 uu____2536
                                                in
                                             let k =
                                               FStar_Syntax_Util.arrow
                                                 (FStar_List.append bs [f]) c
                                                in
                                             ((let uu____2605 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____2605
                                               then
                                                 let uu____2610 =
                                                   FStar_Syntax_Print.term_to_string
                                                     k
                                                    in
                                                 FStar_Util.print1
                                                   "Expected type before unification: %s\n"
                                                   uu____2610
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
                                                let uu____2618 =
                                                  let uu____2621 =
                                                    FStar_All.pipe_right k1
                                                      (FStar_TypeChecker_Normalize.normalize
                                                         [FStar_TypeChecker_Env.Beta;
                                                         FStar_TypeChecker_Env.Eager_unfolding]
                                                         env)
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____2621
                                                    (FStar_Syntax_Subst.close_univ_vars
                                                       stronger_us)
                                                   in
                                                (stronger_us, stronger_t,
                                                  uu____2618))))))))))
                in
             log_combinator "stronger_repr" stronger_repr;
             (let conjunction =
                let conjunction_ts =
                  let uu____2646 =
                    FStar_All.pipe_right ed.FStar_Syntax_Syntax.match_wps
                      FStar_Util.right
                     in
                  uu____2646.FStar_Syntax_Syntax.conjunction  in
                let r =
                  (FStar_Pervasives_Native.snd conjunction_ts).FStar_Syntax_Syntax.pos
                   in
                let uu____2656 =
                  check_and_gen "conjunction" Prims.int_one conjunction_ts
                   in
                match uu____2656 with
                | (conjunction_us,conjunction_t,conjunction_ty) ->
                    let uu____2680 =
                      FStar_Syntax_Subst.open_univ_vars conjunction_us
                        conjunction_t
                       in
                    (match uu____2680 with
                     | (us,t) ->
                         let uu____2699 =
                           FStar_Syntax_Subst.open_univ_vars conjunction_us
                             conjunction_ty
                            in
                         (match uu____2699 with
                          | (uu____2716,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              let uu____2719 = fresh_a_and_u_a "a"  in
                              (match uu____2719 with
                               | (a,u_a) ->
                                   let rest_bs =
                                     let uu____2748 =
                                       let uu____2749 =
                                         FStar_Syntax_Subst.compress ty  in
                                       uu____2749.FStar_Syntax_Syntax.n  in
                                     match uu____2748 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (bs,uu____2761) when
                                         (FStar_List.length bs) >=
                                           (Prims.of_int (4))
                                         ->
                                         let uu____2789 =
                                           FStar_Syntax_Subst.open_binders bs
                                            in
                                         (match uu____2789 with
                                          | (a',uu____2799)::bs1 ->
                                              let uu____2819 =
                                                let uu____2820 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.splitAt
                                                       ((FStar_List.length
                                                           bs1)
                                                          -
                                                          (Prims.of_int (3))))
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2820
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              let uu____2918 =
                                                let uu____2931 =
                                                  let uu____2934 =
                                                    let uu____2935 =
                                                      let uu____2942 =
                                                        let uu____2945 =
                                                          FStar_All.pipe_right
                                                            a
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2945
                                                          FStar_Syntax_Syntax.bv_to_name
                                                         in
                                                      (a', uu____2942)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____2935
                                                     in
                                                  [uu____2934]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____2931
                                                 in
                                              FStar_All.pipe_right uu____2819
                                                uu____2918)
                                     | uu____2966 ->
                                         not_an_arrow_error "conjunction"
                                           (Prims.of_int (4)) ty r
                                      in
                                   let bs = a :: rest_bs  in
                                   let uu____2984 =
                                     let uu____2995 =
                                       let uu____3000 =
                                         FStar_TypeChecker_Env.push_binders
                                           env bs
                                          in
                                       let uu____3001 =
                                         let uu____3002 =
                                           FStar_All.pipe_right a
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_All.pipe_right uu____3002
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       fresh_repr r uu____3000 u_a uu____3001
                                        in
                                     match uu____2995 with
                                     | (repr1,g) ->
                                         let uu____3023 =
                                           let uu____3030 =
                                             FStar_Syntax_Syntax.gen_bv "f"
                                               FStar_Pervasives_Native.None
                                               repr1
                                              in
                                           FStar_All.pipe_right uu____3030
                                             FStar_Syntax_Syntax.mk_binder
                                            in
                                         (uu____3023, g)
                                      in
                                   (match uu____2984 with
                                    | (f_bs,guard_f) ->
                                        let uu____3070 =
                                          let uu____3081 =
                                            let uu____3086 =
                                              FStar_TypeChecker_Env.push_binders
                                                env bs
                                               in
                                            let uu____3087 =
                                              let uu____3088 =
                                                FStar_All.pipe_right a
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right uu____3088
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            fresh_repr r uu____3086 u_a
                                              uu____3087
                                             in
                                          match uu____3081 with
                                          | (repr1,g) ->
                                              let uu____3109 =
                                                let uu____3116 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "g"
                                                    FStar_Pervasives_Native.None
                                                    repr1
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3116
                                                  FStar_Syntax_Syntax.mk_binder
                                                 in
                                              (uu____3109, g)
                                           in
                                        (match uu____3070 with
                                         | (g_bs,guard_g) ->
                                             let p_b =
                                               let uu____3163 =
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "p"
                                                   FStar_Pervasives_Native.None
                                                   FStar_Syntax_Util.ktype0
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3163
                                                 FStar_Syntax_Syntax.mk_binder
                                                in
                                             let uu____3171 =
                                               let uu____3176 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env
                                                   (FStar_List.append bs
                                                      [p_b])
                                                  in
                                               let uu____3195 =
                                                 let uu____3196 =
                                                   FStar_All.pipe_right a
                                                     FStar_Pervasives_Native.fst
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3196
                                                   FStar_Syntax_Syntax.bv_to_name
                                                  in
                                               fresh_repr r uu____3176 u_a
                                                 uu____3195
                                                in
                                             (match uu____3171 with
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
                                                   (let uu____3256 =
                                                      let uu____3259 =
                                                        FStar_All.pipe_right
                                                          k
                                                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                             env)
                                                         in
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        conjunction_us
                                                        uu____3259
                                                       in
                                                    (conjunction_us,
                                                      uu____3256,
                                                      conjunction_ty)))))))))
                 in
              log_combinator "conjunction" conjunction;
              (let tc_action env act =
                 let env01 = env  in
                 let r =
                   (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                    in
                 if
                   (FStar_List.length act.FStar_Syntax_Syntax.action_params)
                     <> Prims.int_zero
                 then
                   (let uu____3291 =
                      let uu____3297 =
                        let uu____3299 =
                          FStar_Syntax_Print.binders_to_string "; "
                            act.FStar_Syntax_Syntax.action_params
                           in
                        FStar_Util.format3
                          "Action %s:%s has non-empty action params (%s)"
                          (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          uu____3299
                         in
                      (FStar_Errors.Fatal_MalformedActionDeclaration,
                        uu____3297)
                       in
                    FStar_Errors.raise_error uu____3291 r)
                 else ();
                 (let uu____3306 =
                    let uu____3311 =
                      FStar_Syntax_Subst.univ_var_opening
                        act.FStar_Syntax_Syntax.action_univs
                       in
                    match uu____3311 with
                    | (usubst,us) ->
                        let uu____3334 =
                          FStar_TypeChecker_Env.push_univ_vars env us  in
                        let uu____3335 =
                          let uu___333_3336 = act  in
                          let uu____3337 =
                            FStar_Syntax_Subst.subst usubst
                              act.FStar_Syntax_Syntax.action_defn
                             in
                          let uu____3338 =
                            FStar_Syntax_Subst.subst usubst
                              act.FStar_Syntax_Syntax.action_typ
                             in
                          {
                            FStar_Syntax_Syntax.action_name =
                              (uu___333_3336.FStar_Syntax_Syntax.action_name);
                            FStar_Syntax_Syntax.action_unqualified_name =
                              (uu___333_3336.FStar_Syntax_Syntax.action_unqualified_name);
                            FStar_Syntax_Syntax.action_univs = us;
                            FStar_Syntax_Syntax.action_params =
                              (uu___333_3336.FStar_Syntax_Syntax.action_params);
                            FStar_Syntax_Syntax.action_defn = uu____3337;
                            FStar_Syntax_Syntax.action_typ = uu____3338
                          }  in
                        (uu____3334, uu____3335)
                     in
                  match uu____3306 with
                  | (env1,act1) ->
                      let act_typ =
                        let uu____3342 =
                          let uu____3343 =
                            FStar_Syntax_Subst.compress
                              act1.FStar_Syntax_Syntax.action_typ
                             in
                          uu____3343.FStar_Syntax_Syntax.n  in
                        match uu____3342 with
                        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                            let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
                            let uu____3369 =
                              FStar_Ident.lid_equals
                                ct.FStar_Syntax_Syntax.effect_name
                                ed.FStar_Syntax_Syntax.mname
                               in
                            if uu____3369
                            then
                              let repr_ts =
                                let uu____3373 = repr  in
                                match uu____3373 with
                                | (us,t,uu____3388) -> (us, t)  in
                              let repr1 =
                                let uu____3406 =
                                  FStar_TypeChecker_Env.inst_tscheme_with
                                    repr_ts ct.FStar_Syntax_Syntax.comp_univs
                                   in
                                FStar_All.pipe_right uu____3406
                                  FStar_Pervasives_Native.snd
                                 in
                              let repr2 =
                                let uu____3418 =
                                  let uu____3423 =
                                    let uu____3424 =
                                      FStar_Syntax_Syntax.as_arg
                                        ct.FStar_Syntax_Syntax.result_typ
                                       in
                                    uu____3424 ::
                                      (ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app repr1
                                    uu____3423
                                   in
                                uu____3418 FStar_Pervasives_Native.None r  in
                              let c1 =
                                let uu____3442 =
                                  let uu____3445 =
                                    FStar_TypeChecker_Env.new_u_univ ()  in
                                  FStar_Pervasives_Native.Some uu____3445  in
                                FStar_Syntax_Syntax.mk_Total' repr2
                                  uu____3442
                                 in
                              FStar_Syntax_Util.arrow bs c1
                            else act1.FStar_Syntax_Syntax.action_typ
                        | uu____3448 -> act1.FStar_Syntax_Syntax.action_typ
                         in
                      let uu____3449 =
                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                          act_typ
                         in
                      (match uu____3449 with
                       | (act_typ1,uu____3457,g_t) ->
                           let uu____3459 =
                             let uu____3466 =
                               let uu___358_3467 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   act_typ1
                                  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___358_3467.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___358_3467.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___358_3467.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___358_3467.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___358_3467.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___358_3467.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___358_3467.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___358_3467.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___358_3467.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___358_3467.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   false;
                                 FStar_TypeChecker_Env.effects =
                                   (uu___358_3467.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___358_3467.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___358_3467.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___358_3467.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___358_3467.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___358_3467.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___358_3467.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___358_3467.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___358_3467.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___358_3467.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___358_3467.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___358_3467.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___358_3467.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___358_3467.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___358_3467.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___358_3467.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___358_3467.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___358_3467.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___358_3467.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___358_3467.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___358_3467.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___358_3467.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___358_3467.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___358_3467.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.try_solve_implicits_hook
                                   =
                                   (uu___358_3467.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___358_3467.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.mpreprocess =
                                   (uu___358_3467.FStar_TypeChecker_Env.mpreprocess);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___358_3467.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___358_3467.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___358_3467.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___358_3467.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___358_3467.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___358_3467.FStar_TypeChecker_Env.nbe);
                                 FStar_TypeChecker_Env.strict_args_tab =
                                   (uu___358_3467.FStar_TypeChecker_Env.strict_args_tab);
                                 FStar_TypeChecker_Env.erasable_types_tab =
                                   (uu___358_3467.FStar_TypeChecker_Env.erasable_types_tab)
                               }  in
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               uu____3466
                               act1.FStar_Syntax_Syntax.action_defn
                              in
                           (match uu____3459 with
                            | (act_defn,uu____3470,g_d) ->
                                ((let uu____3473 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____3473
                                  then
                                    let uu____3478 =
                                      FStar_Syntax_Print.term_to_string
                                        act_defn
                                       in
                                    let uu____3480 =
                                      FStar_Syntax_Print.term_to_string
                                        act_typ1
                                       in
                                    FStar_Util.print2
                                      "Typechecked action definition: %s and action type: %s\n"
                                      uu____3478 uu____3480
                                  else ());
                                 (let uu____3485 =
                                    let act_typ2 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Beta] env1
                                        act_typ1
                                       in
                                    let uu____3493 =
                                      let uu____3494 =
                                        FStar_Syntax_Subst.compress act_typ2
                                         in
                                      uu____3494.FStar_Syntax_Syntax.n  in
                                    match uu____3493 with
                                    | FStar_Syntax_Syntax.Tm_arrow
                                        (bs,uu____3504) ->
                                        let bs1 =
                                          FStar_Syntax_Subst.open_binders bs
                                           in
                                        let env2 =
                                          FStar_TypeChecker_Env.push_binders
                                            env1 bs1
                                           in
                                        let uu____3527 =
                                          FStar_Syntax_Util.type_u ()  in
                                        (match uu____3527 with
                                         | (t,u) ->
                                             let reason =
                                               FStar_Util.format2
                                                 "implicit for return type of action %s:%s"
                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                in
                                             let uu____3543 =
                                               FStar_TypeChecker_Util.new_implicit_var
                                                 reason r env2 t
                                                in
                                             (match uu____3543 with
                                              | (a_tm,uu____3563,g_tm) ->
                                                  let uu____3577 =
                                                    fresh_repr r env2 u a_tm
                                                     in
                                                  (match uu____3577 with
                                                   | (repr1,g) ->
                                                       let uu____3590 =
                                                         let uu____3593 =
                                                           let uu____3596 =
                                                             let uu____3599 =
                                                               FStar_TypeChecker_Env.new_u_univ
                                                                 ()
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____3599
                                                               (fun _3602  ->
                                                                  FStar_Pervasives_Native.Some
                                                                    _3602)
                                                              in
                                                           FStar_Syntax_Syntax.mk_Total'
                                                             repr1 uu____3596
                                                            in
                                                         FStar_Syntax_Util.arrow
                                                           bs1 uu____3593
                                                          in
                                                       let uu____3603 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g g_tm
                                                          in
                                                       (uu____3590,
                                                         uu____3603))))
                                    | uu____3606 ->
                                        let uu____3607 =
                                          let uu____3613 =
                                            let uu____3615 =
                                              FStar_Syntax_Print.term_to_string
                                                act_typ2
                                               in
                                            FStar_Util.format3
                                              "Unexpected non-function type for action %s:%s (%s)"
                                              (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                              (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                              uu____3615
                                             in
                                          (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                            uu____3613)
                                           in
                                        FStar_Errors.raise_error uu____3607 r
                                     in
                                  match uu____3485 with
                                  | (k,g_k) ->
                                      ((let uu____3632 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env1)
                                            (FStar_Options.Other
                                               "LayeredEffects")
                                           in
                                        if uu____3632
                                        then
                                          let uu____3637 =
                                            FStar_Syntax_Print.term_to_string
                                              k
                                             in
                                          FStar_Util.print1
                                            "Expected action type: %s\n"
                                            uu____3637
                                        else ());
                                       (let g =
                                          FStar_TypeChecker_Rel.teq env1
                                            act_typ1 k
                                           in
                                        FStar_List.iter
                                          (FStar_TypeChecker_Rel.force_trivial_guard
                                             env1) [g_t; g_d; g_k; g];
                                        (let uu____3645 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other
                                                "LayeredEffects")
                                            in
                                         if uu____3645
                                         then
                                           let uu____3650 =
                                             FStar_Syntax_Print.term_to_string
                                               k
                                              in
                                           FStar_Util.print1
                                             "Expected action type after unification: %s\n"
                                             uu____3650
                                         else ());
                                        (let act_typ2 =
                                           let err_msg t =
                                             let uu____3663 =
                                               FStar_Syntax_Print.term_to_string
                                                 t
                                                in
                                             FStar_Util.format3
                                               "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                               uu____3663
                                              in
                                           let repr_args t =
                                             let uu____3684 =
                                               let uu____3685 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____3685.FStar_Syntax_Syntax.n
                                                in
                                             match uu____3684 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (head1,a::is) ->
                                                 let uu____3737 =
                                                   let uu____3738 =
                                                     FStar_Syntax_Subst.compress
                                                       head1
                                                      in
                                                   uu____3738.FStar_Syntax_Syntax.n
                                                    in
                                                 (match uu____3737 with
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                      (uu____3747,us) ->
                                                      (us,
                                                        (FStar_Pervasives_Native.fst
                                                           a), is)
                                                  | uu____3757 ->
                                                      let uu____3758 =
                                                        let uu____3764 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____3764)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____3758 r)
                                             | uu____3773 ->
                                                 let uu____3774 =
                                                   let uu____3780 = err_msg t
                                                      in
                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                     uu____3780)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____3774 r
                                              in
                                           let k1 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.Beta]
                                               env1 k
                                              in
                                           let uu____3790 =
                                             let uu____3791 =
                                               FStar_Syntax_Subst.compress k1
                                                in
                                             uu____3791.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3790 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs,c) ->
                                               let uu____3816 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs c
                                                  in
                                               (match uu____3816 with
                                                | (bs1,c1) ->
                                                    let uu____3823 =
                                                      repr_args
                                                        (FStar_Syntax_Util.comp_result
                                                           c1)
                                                       in
                                                    (match uu____3823 with
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
                                                         let uu____3834 =
                                                           FStar_Syntax_Syntax.mk_Comp
                                                             ct
                                                            in
                                                         FStar_Syntax_Util.arrow
                                                           bs1 uu____3834))
                                           | uu____3837 ->
                                               let uu____3838 =
                                                 let uu____3844 = err_msg k1
                                                    in
                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                   uu____3844)
                                                  in
                                               FStar_Errors.raise_error
                                                 uu____3838 r
                                            in
                                         (let uu____3848 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env1)
                                              (FStar_Options.Other
                                                 "LayeredEffects")
                                             in
                                          if uu____3848
                                          then
                                            let uu____3853 =
                                              FStar_Syntax_Print.term_to_string
                                                act_typ2
                                               in
                                            FStar_Util.print1
                                              "Action type after injecting it into the monad: %s\n"
                                              uu____3853
                                          else ());
                                         (let act2 =
                                            let uu____3859 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env1 act_defn
                                               in
                                            match uu____3859 with
                                            | (us,act_defn1) ->
                                                if
                                                  act1.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then
                                                  let uu___431_3873 = act1
                                                     in
                                                  let uu____3874 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      us act_typ2
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.action_name
                                                      =
                                                      (uu___431_3873.FStar_Syntax_Syntax.action_name);
                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                      =
                                                      (uu___431_3873.FStar_Syntax_Syntax.action_unqualified_name);
                                                    FStar_Syntax_Syntax.action_univs
                                                      = us;
                                                    FStar_Syntax_Syntax.action_params
                                                      =
                                                      (uu___431_3873.FStar_Syntax_Syntax.action_params);
                                                    FStar_Syntax_Syntax.action_defn
                                                      = act_defn1;
                                                    FStar_Syntax_Syntax.action_typ
                                                      = uu____3874
                                                  }
                                                else
                                                  (let uu____3877 =
                                                     ((FStar_List.length us)
                                                        =
                                                        (FStar_List.length
                                                           act1.FStar_Syntax_Syntax.action_univs))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1  ->
                                                             fun u2  ->
                                                               let uu____3884
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2
                                                                  in
                                                               uu____3884 =
                                                                 Prims.int_zero)
                                                          us
                                                          act1.FStar_Syntax_Syntax.action_univs)
                                                      in
                                                   if uu____3877
                                                   then
                                                     let uu___436_3889 = act1
                                                        in
                                                     let uu____3890 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         act1.FStar_Syntax_Syntax.action_univs
                                                         act_typ2
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___436_3889.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___436_3889.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         =
                                                         (uu___436_3889.FStar_Syntax_Syntax.action_univs);
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___436_3889.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = act_defn1;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____3890
                                                     }
                                                   else
                                                     (let uu____3893 =
                                                        let uu____3899 =
                                                          let uu____3901 =
                                                            FStar_Syntax_Print.univ_names_to_string
                                                              us
                                                             in
                                                          let uu____3903 =
                                                            FStar_Syntax_Print.univ_names_to_string
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                             in
                                                          FStar_Util.format4
                                                            "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                            (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                            (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                            uu____3901
                                                            uu____3903
                                                           in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____3899)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____3893 r))
                                             in
                                          act2)))))))))
                  in
               let fst1 uu____3926 =
                 match uu____3926 with | (a,uu____3942,uu____3943) -> a  in
               let snd1 uu____3975 =
                 match uu____3975 with | (uu____3990,b,uu____3992) -> b  in
               let thd uu____4024 =
                 match uu____4024 with | (uu____4039,uu____4040,c) -> c  in
               let uu___454_4054 = ed  in
               let uu____4055 =
                 FStar_All.pipe_right
                   ((fst1 stronger_repr), (snd1 stronger_repr))
                   (fun _4064  -> FStar_Pervasives_Native.Some _4064)
                  in
               let uu____4065 =
                 FStar_List.map (tc_action env0)
                   ed.FStar_Syntax_Syntax.actions
                  in
               {
                 FStar_Syntax_Syntax.is_layered =
                   (uu___454_4054.FStar_Syntax_Syntax.is_layered);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___454_4054.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.mname =
                   (uu___454_4054.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.univs =
                   (uu___454_4054.FStar_Syntax_Syntax.univs);
                 FStar_Syntax_Syntax.binders =
                   (uu___454_4054.FStar_Syntax_Syntax.binders);
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
                   (uu___454_4054.FStar_Syntax_Syntax.trivial);
                 FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
                 FStar_Syntax_Syntax.return_repr =
                   ((fst1 return_repr), (snd1 return_repr));
                 FStar_Syntax_Syntax.bind_repr =
                   ((fst1 bind_repr), (snd1 bind_repr));
                 FStar_Syntax_Syntax.stronger_repr = uu____4055;
                 FStar_Syntax_Syntax.actions = uu____4065;
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___454_4054.FStar_Syntax_Syntax.eff_attrs)
               })))))))
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____4116 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____4116 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____4143 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____4143
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____4165 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____4165
         then
           let uu____4170 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____4170
         else ());
        (let uu____4176 =
           let uu____4181 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____4181 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____4205 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____4205  in
               let uu____4206 =
                 let uu____4213 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____4213 bs  in
               (match uu____4206 with
                | (bs1,uu____4219,uu____4220) ->
                    let uu____4221 =
                      let tmp_t =
                        let uu____4231 =
                          let uu____4234 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _4239  ->
                                 FStar_Pervasives_Native.Some _4239)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____4234
                           in
                        FStar_Syntax_Util.arrow bs1 uu____4231  in
                      let uu____4240 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____4240 with
                      | (us,tmp_t1) ->
                          let uu____4257 =
                            let uu____4258 =
                              let uu____4259 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____4259
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____4258
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____4257)
                       in
                    (match uu____4221 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____4328 ->
                              let uu____4331 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____4338 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____4338 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____4331
                              then (us, bs2)
                              else
                                (let uu____4349 =
                                   let uu____4355 =
                                     let uu____4357 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____4359 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____4357 uu____4359
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____4355)
                                    in
                                 let uu____4363 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____4349
                                   uu____4363))))
            in
         match uu____4176 with
         | (us,bs) ->
             let ed1 =
               let uu___495_4371 = ed  in
               {
                 FStar_Syntax_Syntax.is_layered =
                   (uu___495_4371.FStar_Syntax_Syntax.is_layered);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___495_4371.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.mname =
                   (uu___495_4371.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___495_4371.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.ret_wp =
                   (uu___495_4371.FStar_Syntax_Syntax.ret_wp);
                 FStar_Syntax_Syntax.bind_wp =
                   (uu___495_4371.FStar_Syntax_Syntax.bind_wp);
                 FStar_Syntax_Syntax.stronger =
                   (uu___495_4371.FStar_Syntax_Syntax.stronger);
                 FStar_Syntax_Syntax.match_wps =
                   (uu___495_4371.FStar_Syntax_Syntax.match_wps);
                 FStar_Syntax_Syntax.trivial =
                   (uu___495_4371.FStar_Syntax_Syntax.trivial);
                 FStar_Syntax_Syntax.repr =
                   (uu___495_4371.FStar_Syntax_Syntax.repr);
                 FStar_Syntax_Syntax.return_repr =
                   (uu___495_4371.FStar_Syntax_Syntax.return_repr);
                 FStar_Syntax_Syntax.bind_repr =
                   (uu___495_4371.FStar_Syntax_Syntax.bind_repr);
                 FStar_Syntax_Syntax.stronger_repr =
                   (uu___495_4371.FStar_Syntax_Syntax.stronger_repr);
                 FStar_Syntax_Syntax.actions =
                   (uu___495_4371.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___495_4371.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____4372 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____4372 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____4391 =
                    let uu____4396 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____4396  in
                  (match uu____4391 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____4417 =
                           match uu____4417 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____4437 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____4437 t  in
                               let uu____4446 =
                                 let uu____4447 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____4447 t1  in
                               (us1, uu____4446)
                            in
                         let uu___509_4452 = ed1  in
                         let uu____4453 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____4454 = op ed1.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____4455 = op ed1.FStar_Syntax_Syntax.bind_wp
                            in
                         let uu____4456 = op ed1.FStar_Syntax_Syntax.stronger
                            in
                         let uu____4457 =
                           FStar_Syntax_Util.map_match_wps op
                             ed1.FStar_Syntax_Syntax.match_wps
                            in
                         let uu____4462 =
                           FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                             op
                            in
                         let uu____4465 = op ed1.FStar_Syntax_Syntax.repr  in
                         let uu____4466 =
                           op ed1.FStar_Syntax_Syntax.return_repr  in
                         let uu____4467 =
                           op ed1.FStar_Syntax_Syntax.bind_repr  in
                         let uu____4468 =
                           FStar_List.map
                             (fun a  ->
                                let uu___512_4476 = a  in
                                let uu____4477 =
                                  let uu____4478 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____4478  in
                                let uu____4489 =
                                  let uu____4490 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____4490  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___512_4476.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___512_4476.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___512_4476.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___512_4476.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____4477;
                                  FStar_Syntax_Syntax.action_typ = uu____4489
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.is_layered =
                             (uu___509_4452.FStar_Syntax_Syntax.is_layered);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___509_4452.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.mname =
                             (uu___509_4452.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.univs =
                             (uu___509_4452.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___509_4452.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____4453;
                           FStar_Syntax_Syntax.ret_wp = uu____4454;
                           FStar_Syntax_Syntax.bind_wp = uu____4455;
                           FStar_Syntax_Syntax.stronger = uu____4456;
                           FStar_Syntax_Syntax.match_wps = uu____4457;
                           FStar_Syntax_Syntax.trivial = uu____4462;
                           FStar_Syntax_Syntax.repr = uu____4465;
                           FStar_Syntax_Syntax.return_repr = uu____4466;
                           FStar_Syntax_Syntax.bind_repr = uu____4467;
                           FStar_Syntax_Syntax.stronger_repr =
                             FStar_Pervasives_Native.None;
                           FStar_Syntax_Syntax.actions = uu____4468;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___509_4452.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____4502 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____4502
                         then
                           let uu____4507 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____4507
                         else ());
                        (let env =
                           let uu____4514 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____4514
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____4549 k =
                           match uu____4549 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____4569 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____4569 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____4578 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          tc_check_trivial_guard uu____4578
                                            t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____4579 =
                                            let uu____4586 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____4586 t1
                                             in
                                          (match uu____4579 with
                                           | (t2,uu____4588,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____4591 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____4591 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____4607 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____4609 =
                                                 let uu____4611 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____4611
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____4607 uu____4609
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____4626 ->
                                               let uu____4627 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____4634 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____4634 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____4627
                                               then (g_us, t3)
                                               else
                                                 (let uu____4645 =
                                                    let uu____4651 =
                                                      let uu____4653 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____4655 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____4653
                                                        uu____4655
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____4651)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____4645
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____4663 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____4663
                          then
                            let uu____4668 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____4668
                          else ());
                         (let fresh_a_and_wp uu____4684 =
                            let fail1 t =
                              let uu____4697 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____4697
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____4713 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____4713 with
                            | (uu____4724,signature1) ->
                                let uu____4726 =
                                  let uu____4727 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____4727.FStar_Syntax_Syntax.n  in
                                (match uu____4726 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____4737) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____4766)::(wp,uu____4768)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____4797 -> fail1 signature1)
                                 | uu____4798 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____4812 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____4812
                            then
                              let uu____4817 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____4817
                            else ()  in
                          let ret_wp =
                            let uu____4823 = fresh_a_and_wp ()  in
                            match uu____4823 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____4839 =
                                    let uu____4848 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____4855 =
                                      let uu____4864 =
                                        let uu____4871 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____4871
                                         in
                                      [uu____4864]  in
                                    uu____4848 :: uu____4855  in
                                  let uu____4890 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____4839
                                    uu____4890
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None
                                  ed2.FStar_Syntax_Syntax.ret_wp
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____4898 = fresh_a_and_wp ()  in
                             match uu____4898 with
                             | (a,wp_sort_a) ->
                                 let uu____4911 = fresh_a_and_wp ()  in
                                 (match uu____4911 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____4927 =
                                          let uu____4936 =
                                            let uu____4943 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____4943
                                             in
                                          [uu____4936]  in
                                        let uu____4956 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____4927
                                          uu____4956
                                         in
                                      let k =
                                        let uu____4962 =
                                          let uu____4971 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____4978 =
                                            let uu____4987 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____4994 =
                                              let uu____5003 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____5010 =
                                                let uu____5019 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____5026 =
                                                  let uu____5035 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____5035]  in
                                                uu____5019 :: uu____5026  in
                                              uu____5003 :: uu____5010  in
                                            uu____4987 :: uu____4994  in
                                          uu____4971 :: uu____4978  in
                                        let uu____5078 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____4962
                                          uu____5078
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____5086 = fresh_a_and_wp ()  in
                              match uu____5086 with
                              | (a,wp_sort_a) ->
                                  let uu____5099 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____5099 with
                                   | (t,uu____5105) ->
                                       let k =
                                         let uu____5109 =
                                           let uu____5118 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____5125 =
                                             let uu____5134 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____5141 =
                                               let uu____5150 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____5150]  in
                                             uu____5134 :: uu____5141  in
                                           uu____5118 :: uu____5125  in
                                         let uu____5181 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____5109
                                           uu____5181
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         ed2.FStar_Syntax_Syntax.stronger
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let match_wps =
                               let uu____5193 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   ed2.FStar_Syntax_Syntax.match_wps
                                  in
                               match uu____5193 with
                               | (if_then_else1,ite_wp,close_wp) ->
                                   let if_then_else2 =
                                     let uu____5208 = fresh_a_and_wp ()  in
                                     match uu____5208 with
                                     | (a,wp_sort_a) ->
                                         let p =
                                           let uu____5222 =
                                             let uu____5225 =
                                               FStar_Ident.range_of_lid
                                                 ed2.FStar_Syntax_Syntax.mname
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____5225
                                              in
                                           let uu____5226 =
                                             let uu____5227 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_right uu____5227
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____5222 uu____5226
                                            in
                                         let k =
                                           let uu____5239 =
                                             let uu____5248 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____5255 =
                                               let uu____5264 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   p
                                                  in
                                               let uu____5271 =
                                                 let uu____5280 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 let uu____5287 =
                                                   let uu____5296 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       wp_sort_a
                                                      in
                                                   [uu____5296]  in
                                                 uu____5280 :: uu____5287  in
                                               uu____5264 :: uu____5271  in
                                             uu____5248 :: uu____5255  in
                                           let uu____5333 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____5239
                                             uu____5333
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
                                       let uu____5341 = fresh_a_and_wp ()  in
                                       match uu____5341 with
                                       | (a,wp_sort_a) ->
                                           let k =
                                             let uu____5357 =
                                               let uu____5366 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____5373 =
                                                 let uu____5382 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____5382]  in
                                               uu____5366 :: uu____5373  in
                                             let uu____5407 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 wp_sort_a
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____5357 uu____5407
                                              in
                                           check_and_gen' "ite_wp"
                                             Prims.int_one
                                             FStar_Pervasives_Native.None
                                             ite_wp
                                             (FStar_Pervasives_Native.Some k)
                                        in
                                     log_combinator "ite_wp" ite_wp1;
                                     (let close_wp1 =
                                        let uu____5415 = fresh_a_and_wp ()
                                           in
                                        match uu____5415 with
                                        | (a,wp_sort_a) ->
                                            let b =
                                              let uu____5429 =
                                                let uu____5432 =
                                                  FStar_Ident.range_of_lid
                                                    ed2.FStar_Syntax_Syntax.mname
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____5432
                                                 in
                                              let uu____5433 =
                                                let uu____5434 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____5434
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.new_bv
                                                uu____5429 uu____5433
                                               in
                                            let wp_sort_b_a =
                                              let uu____5446 =
                                                let uu____5455 =
                                                  let uu____5462 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      b
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____5462
                                                   in
                                                [uu____5455]  in
                                              let uu____5475 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5446 uu____5475
                                               in
                                            let k =
                                              let uu____5481 =
                                                let uu____5490 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____5497 =
                                                  let uu____5506 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____5513 =
                                                    let uu____5522 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_b_a
                                                       in
                                                    [uu____5522]  in
                                                  uu____5506 :: uu____5513
                                                   in
                                                uu____5490 :: uu____5497  in
                                              let uu____5553 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5481 uu____5553
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
                               let uu____5563 = fresh_a_and_wp ()  in
                               match uu____5563 with
                               | (a,wp_sort_a) ->
                                   let uu____5578 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____5578 with
                                    | (t,uu____5586) ->
                                        let k =
                                          let uu____5590 =
                                            let uu____5599 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5606 =
                                              let uu____5615 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              [uu____5615]  in
                                            uu____5599 :: uu____5606  in
                                          let uu____5640 =
                                            FStar_Syntax_Syntax.mk_GTotal t
                                             in
                                          FStar_Syntax_Util.arrow uu____5590
                                            uu____5640
                                           in
                                        let trivial =
                                          let uu____5644 =
                                            FStar_All.pipe_right
                                              ed2.FStar_Syntax_Syntax.trivial
                                              FStar_Util.must
                                             in
                                          check_and_gen' "trivial"
                                            Prims.int_one
                                            FStar_Pervasives_Native.None
                                            uu____5644
                                            (FStar_Pervasives_Native.Some k)
                                           in
                                        (log_combinator "trivial" trivial;
                                         FStar_Pervasives_Native.Some trivial))
                                in
                             let uu____5659 =
                               let uu____5670 =
                                 let uu____5671 =
                                   FStar_Syntax_Subst.compress
                                     (FStar_Pervasives_Native.snd
                                        ed2.FStar_Syntax_Syntax.repr)
                                    in
                                 uu____5671.FStar_Syntax_Syntax.n  in
                               match uu____5670 with
                               | FStar_Syntax_Syntax.Tm_unknown  ->
                                   ((ed2.FStar_Syntax_Syntax.repr),
                                     (ed2.FStar_Syntax_Syntax.return_repr),
                                     (ed2.FStar_Syntax_Syntax.bind_repr),
                                     (ed2.FStar_Syntax_Syntax.actions))
                               | uu____5690 ->
                                   let repr =
                                     let uu____5692 = fresh_a_and_wp ()  in
                                     match uu____5692 with
                                     | (a,wp_sort_a) ->
                                         let uu____5705 =
                                           FStar_Syntax_Util.type_u ()  in
                                         (match uu____5705 with
                                          | (t,uu____5711) ->
                                              let k =
                                                let uu____5715 =
                                                  let uu____5724 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____5731 =
                                                    let uu____5740 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a
                                                       in
                                                    [uu____5740]  in
                                                  uu____5724 :: uu____5731
                                                   in
                                                let uu____5765 =
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5715 uu____5765
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
                                       let uu____5785 =
                                         FStar_TypeChecker_Env.inst_tscheme
                                           repr
                                          in
                                       match uu____5785 with
                                       | (uu____5792,repr1) ->
                                           let repr2 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.EraseUniverses;
                                               FStar_TypeChecker_Env.AllowUnboundUniverses]
                                               env repr1
                                              in
                                           let uu____5795 =
                                             let uu____5802 =
                                               let uu____5803 =
                                                 let uu____5820 =
                                                   let uu____5831 =
                                                     FStar_All.pipe_right t
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   let uu____5848 =
                                                     let uu____5859 =
                                                       FStar_All.pipe_right
                                                         wp
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____5859]  in
                                                   uu____5831 :: uu____5848
                                                    in
                                                 (repr2, uu____5820)  in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____5803
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____5802
                                              in
                                           uu____5795
                                             FStar_Pervasives_Native.None
                                             FStar_Range.dummyRange
                                        in
                                     let mk_repr a wp =
                                       let uu____5925 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_repr' uu____5925 wp  in
                                     let destruct_repr t =
                                       let uu____5940 =
                                         let uu____5941 =
                                           FStar_Syntax_Subst.compress t  in
                                         uu____5941.FStar_Syntax_Syntax.n  in
                                       match uu____5940 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____5952,(t1,uu____5954)::
                                            (wp,uu____5956)::[])
                                           -> (t1, wp)
                                       | uu____6015 ->
                                           failwith "Unexpected repr type"
                                        in
                                     let return_repr =
                                       let uu____6026 = fresh_a_and_wp ()  in
                                       match uu____6026 with
                                       | (a,uu____6034) ->
                                           let x_a =
                                             let uu____6040 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             FStar_Syntax_Syntax.gen_bv "x_a"
                                               FStar_Pervasives_Native.None
                                               uu____6040
                                              in
                                           let res =
                                             let wp =
                                               let uu____6048 =
                                                 let uu____6053 =
                                                   let uu____6054 =
                                                     FStar_TypeChecker_Env.inst_tscheme
                                                       ret_wp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6054
                                                     FStar_Pervasives_Native.snd
                                                    in
                                                 let uu____6063 =
                                                   let uu____6064 =
                                                     let uu____6073 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____6073
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   let uu____6082 =
                                                     let uu____6093 =
                                                       let uu____6102 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____6102
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____6093]  in
                                                   uu____6064 :: uu____6082
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   uu____6053 uu____6063
                                                  in
                                               uu____6048
                                                 FStar_Pervasives_Native.None
                                                 FStar_Range.dummyRange
                                                in
                                             mk_repr a wp  in
                                           let k =
                                             let uu____6138 =
                                               let uu____6147 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6154 =
                                                 let uu____6163 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x_a
                                                    in
                                                 [uu____6163]  in
                                               uu____6147 :: uu____6154  in
                                             let uu____6188 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 res
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6138 uu____6188
                                              in
                                           let uu____6191 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env k
                                              in
                                           (match uu____6191 with
                                            | (k1,uu____6199,uu____6200) ->
                                                let env1 =
                                                  let uu____6204 =
                                                    FStar_TypeChecker_Env.set_range
                                                      env
                                                      (FStar_Pervasives_Native.snd
                                                         ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____6204
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
                                          let uu____6215 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____6215
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____6216 = fresh_a_and_wp ()
                                           in
                                        match uu____6216 with
                                        | (a,wp_sort_a) ->
                                            let uu____6229 =
                                              fresh_a_and_wp ()  in
                                            (match uu____6229 with
                                             | (b,wp_sort_b) ->
                                                 let wp_sort_a_b =
                                                   let uu____6245 =
                                                     let uu____6254 =
                                                       let uu____6261 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a
                                                          in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____6261
                                                        in
                                                     [uu____6254]  in
                                                   let uu____6274 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       wp_sort_b
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6245 uu____6274
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
                                                   let uu____6282 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "x_a"
                                                     FStar_Pervasives_Native.None
                                                     uu____6282
                                                    in
                                                 let wp_g_x =
                                                   let uu____6287 =
                                                     let uu____6292 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_g
                                                        in
                                                     let uu____6293 =
                                                       let uu____6294 =
                                                         let uu____6303 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x_a
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____6303
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____6294]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____6292 uu____6293
                                                      in
                                                   uu____6287
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 let res =
                                                   let wp =
                                                     let uu____6334 =
                                                       let uu____6339 =
                                                         let uu____6340 =
                                                           FStar_TypeChecker_Env.inst_tscheme
                                                             bind_wp
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____6340
                                                           FStar_Pervasives_Native.snd
                                                          in
                                                       let uu____6349 =
                                                         let uu____6350 =
                                                           let uu____6353 =
                                                             let uu____6356 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 a
                                                                in
                                                             let uu____6357 =
                                                               let uu____6360
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   b
                                                                  in
                                                               let uu____6361
                                                                 =
                                                                 let uu____6364
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                    in
                                                                 let uu____6365
                                                                   =
                                                                   let uu____6368
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                   [uu____6368]
                                                                    in
                                                                 uu____6364
                                                                   ::
                                                                   uu____6365
                                                                  in
                                                               uu____6360 ::
                                                                 uu____6361
                                                                in
                                                             uu____6356 ::
                                                               uu____6357
                                                              in
                                                           r :: uu____6353
                                                            in
                                                         FStar_List.map
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6350
                                                          in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____6339
                                                         uu____6349
                                                        in
                                                     uu____6334
                                                       FStar_Pervasives_Native.None
                                                       FStar_Range.dummyRange
                                                      in
                                                   mk_repr b wp  in
                                                 let maybe_range_arg =
                                                   let uu____6386 =
                                                     FStar_Util.for_some
                                                       (FStar_Syntax_Util.attr_eq
                                                          FStar_Syntax_Util.dm4f_bind_range_attr)
                                                       ed2.FStar_Syntax_Syntax.eff_attrs
                                                      in
                                                   if uu____6386
                                                   then
                                                     let uu____6397 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     let uu____6404 =
                                                       let uu____6413 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           FStar_Syntax_Syntax.t_range
                                                          in
                                                       [uu____6413]  in
                                                     uu____6397 :: uu____6404
                                                   else []  in
                                                 let k =
                                                   let uu____6449 =
                                                     let uu____6458 =
                                                       let uu____6467 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           a
                                                          in
                                                       let uu____6474 =
                                                         let uu____6483 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             b
                                                            in
                                                         [uu____6483]  in
                                                       uu____6467 ::
                                                         uu____6474
                                                        in
                                                     let uu____6508 =
                                                       let uu____6517 =
                                                         let uu____6526 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             wp_f
                                                            in
                                                         let uu____6533 =
                                                           let uu____6542 =
                                                             let uu____6549 =
                                                               let uu____6550
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               mk_repr a
                                                                 uu____6550
                                                                in
                                                             FStar_Syntax_Syntax.null_binder
                                                               uu____6549
                                                              in
                                                           let uu____6551 =
                                                             let uu____6560 =
                                                               FStar_Syntax_Syntax.mk_binder
                                                                 wp_g
                                                                in
                                                             let uu____6567 =
                                                               let uu____6576
                                                                 =
                                                                 let uu____6583
                                                                   =
                                                                   let uu____6584
                                                                    =
                                                                    let uu____6593
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____6593]
                                                                     in
                                                                   let uu____6612
                                                                    =
                                                                    let uu____6615
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____6615
                                                                     in
                                                                   FStar_Syntax_Util.arrow
                                                                    uu____6584
                                                                    uu____6612
                                                                    in
                                                                 FStar_Syntax_Syntax.null_binder
                                                                   uu____6583
                                                                  in
                                                               [uu____6576]
                                                                in
                                                             uu____6560 ::
                                                               uu____6567
                                                              in
                                                           uu____6542 ::
                                                             uu____6551
                                                            in
                                                         uu____6526 ::
                                                           uu____6533
                                                          in
                                                       FStar_List.append
                                                         maybe_range_arg
                                                         uu____6517
                                                        in
                                                     FStar_List.append
                                                       uu____6458 uu____6508
                                                      in
                                                   let uu____6660 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       res
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6449 uu____6660
                                                    in
                                                 let uu____6663 =
                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                     env k
                                                    in
                                                 (match uu____6663 with
                                                  | (k1,uu____6671,uu____6672)
                                                      ->
                                                      let env1 =
                                                        FStar_TypeChecker_Env.set_range
                                                          env
                                                          (FStar_Pervasives_Native.snd
                                                             ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                         in
                                                      let env2 =
                                                        FStar_All.pipe_right
                                                          (let uu___710_6684
                                                             = env1  in
                                                           {
                                                             FStar_TypeChecker_Env.solver
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.solver);
                                                             FStar_TypeChecker_Env.range
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.range);
                                                             FStar_TypeChecker_Env.curmodule
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.curmodule);
                                                             FStar_TypeChecker_Env.gamma
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.gamma);
                                                             FStar_TypeChecker_Env.gamma_sig
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.gamma_sig);
                                                             FStar_TypeChecker_Env.gamma_cache
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.gamma_cache);
                                                             FStar_TypeChecker_Env.modules
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.modules);
                                                             FStar_TypeChecker_Env.expected_typ
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.expected_typ);
                                                             FStar_TypeChecker_Env.sigtab
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.sigtab);
                                                             FStar_TypeChecker_Env.attrtab
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.attrtab);
                                                             FStar_TypeChecker_Env.instantiate_imp
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.instantiate_imp);
                                                             FStar_TypeChecker_Env.effects
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.effects);
                                                             FStar_TypeChecker_Env.generalize
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.generalize);
                                                             FStar_TypeChecker_Env.letrecs
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.letrecs);
                                                             FStar_TypeChecker_Env.top_level
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.top_level);
                                                             FStar_TypeChecker_Env.check_uvars
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.check_uvars);
                                                             FStar_TypeChecker_Env.use_eq
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.use_eq);
                                                             FStar_TypeChecker_Env.is_iface
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.is_iface);
                                                             FStar_TypeChecker_Env.admit
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.admit);
                                                             FStar_TypeChecker_Env.lax
                                                               = true;
                                                             FStar_TypeChecker_Env.lax_universes
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.lax_universes);
                                                             FStar_TypeChecker_Env.phase1
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.phase1);
                                                             FStar_TypeChecker_Env.failhard
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.failhard);
                                                             FStar_TypeChecker_Env.nosynth
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.nosynth);
                                                             FStar_TypeChecker_Env.uvar_subtyping
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.uvar_subtyping);
                                                             FStar_TypeChecker_Env.tc_term
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.tc_term);
                                                             FStar_TypeChecker_Env.type_of
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.type_of);
                                                             FStar_TypeChecker_Env.universe_of
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.universe_of);
                                                             FStar_TypeChecker_Env.check_type_of
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.check_type_of);
                                                             FStar_TypeChecker_Env.use_bv_sorts
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.use_bv_sorts);
                                                             FStar_TypeChecker_Env.qtbl_name_and_index
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                             FStar_TypeChecker_Env.normalized_eff_names
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.normalized_eff_names);
                                                             FStar_TypeChecker_Env.fv_delta_depths
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.fv_delta_depths);
                                                             FStar_TypeChecker_Env.proof_ns
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.proof_ns);
                                                             FStar_TypeChecker_Env.synth_hook
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.synth_hook);
                                                             FStar_TypeChecker_Env.try_solve_implicits_hook
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                             FStar_TypeChecker_Env.splice
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.splice);
                                                             FStar_TypeChecker_Env.mpreprocess
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.mpreprocess);
                                                             FStar_TypeChecker_Env.postprocess
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.postprocess);
                                                             FStar_TypeChecker_Env.is_native_tactic
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.is_native_tactic);
                                                             FStar_TypeChecker_Env.identifier_info
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.identifier_info);
                                                             FStar_TypeChecker_Env.tc_hooks
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.tc_hooks);
                                                             FStar_TypeChecker_Env.dsenv
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.dsenv);
                                                             FStar_TypeChecker_Env.nbe
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.nbe);
                                                             FStar_TypeChecker_Env.strict_args_tab
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.strict_args_tab);
                                                             FStar_TypeChecker_Env.erasable_types_tab
                                                               =
                                                               (uu___710_6684.FStar_TypeChecker_Env.erasable_types_tab)
                                                           })
                                                          (fun _6686  ->
                                                             FStar_Pervasives_Native.Some
                                                               _6686)
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
                                           (let uu____6713 =
                                              if
                                                act.FStar_Syntax_Syntax.action_univs
                                                  = []
                                              then (env, act)
                                              else
                                                (let uu____6727 =
                                                   FStar_Syntax_Subst.univ_var_opening
                                                     act.FStar_Syntax_Syntax.action_univs
                                                    in
                                                 match uu____6727 with
                                                 | (usubst,uvs) ->
                                                     let uu____6750 =
                                                       FStar_TypeChecker_Env.push_univ_vars
                                                         env uvs
                                                        in
                                                     let uu____6751 =
                                                       let uu___723_6752 =
                                                         act  in
                                                       let uu____6753 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____6754 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___723_6752.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___723_6752.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = uvs;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___723_6752.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = uu____6753;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____6754
                                                       }  in
                                                     (uu____6750, uu____6751))
                                               in
                                            match uu____6713 with
                                            | (env1,act1) ->
                                                let act_typ =
                                                  let uu____6758 =
                                                    let uu____6759 =
                                                      FStar_Syntax_Subst.compress
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                       in
                                                    uu____6759.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____6758 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs1,c) ->
                                                      let c1 =
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                          c
                                                         in
                                                      let uu____6785 =
                                                        FStar_Ident.lid_equals
                                                          c1.FStar_Syntax_Syntax.effect_name
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      if uu____6785
                                                      then
                                                        let uu____6788 =
                                                          let uu____6791 =
                                                            let uu____6792 =
                                                              let uu____6793
                                                                =
                                                                FStar_List.hd
                                                                  c1.FStar_Syntax_Syntax.effect_args
                                                                 in
                                                              FStar_Pervasives_Native.fst
                                                                uu____6793
                                                               in
                                                            mk_repr'
                                                              c1.FStar_Syntax_Syntax.result_typ
                                                              uu____6792
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total
                                                            uu____6791
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          bs1 uu____6788
                                                      else
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                  | uu____6816 ->
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                   in
                                                let uu____6817 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env1 act_typ
                                                   in
                                                (match uu____6817 with
                                                 | (act_typ1,uu____6825,g_t)
                                                     ->
                                                     let env' =
                                                       let uu___740_6828 =
                                                         FStar_TypeChecker_Env.set_expected_typ
                                                           env1 act_typ1
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           = false;
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.lax);
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.try_solve_implicits_hook
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.mpreprocess
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.mpreprocess);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.nbe);
                                                         FStar_TypeChecker_Env.strict_args_tab
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.strict_args_tab);
                                                         FStar_TypeChecker_Env.erasable_types_tab
                                                           =
                                                           (uu___740_6828.FStar_TypeChecker_Env.erasable_types_tab)
                                                       }  in
                                                     ((let uu____6831 =
                                                         FStar_TypeChecker_Env.debug
                                                           env1
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____6831
                                                       then
                                                         let uu____6835 =
                                                           FStar_Ident.text_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name
                                                            in
                                                         let uu____6837 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____6839 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act_typ1
                                                            in
                                                         FStar_Util.print3
                                                           "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                           uu____6835
                                                           uu____6837
                                                           uu____6839
                                                       else ());
                                                      (let uu____6844 =
                                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                           env'
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       match uu____6844 with
                                                       | (act_defn,uu____6852,g_a)
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
                                                           let uu____6856 =
                                                             let act_typ3 =
                                                               FStar_Syntax_Subst.compress
                                                                 act_typ2
                                                                in
                                                             match act_typ3.FStar_Syntax_Syntax.n
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs1,c) ->
                                                                 let uu____6892
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs1 c
                                                                    in
                                                                 (match uu____6892
                                                                  with
                                                                  | (bs2,uu____6904)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6911
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6911
                                                                     in
                                                                    let uu____6914
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____6914
                                                                    with
                                                                    | 
                                                                    (k1,uu____6928,g)
                                                                    ->
                                                                    (k1, g)))
                                                             | uu____6932 ->
                                                                 let uu____6933
                                                                   =
                                                                   let uu____6939
                                                                    =
                                                                    let uu____6941
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____6943
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____6941
                                                                    uu____6943
                                                                     in
                                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____6939)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____6933
                                                                   act_defn1.FStar_Syntax_Syntax.pos
                                                              in
                                                           (match uu____6856
                                                            with
                                                            | (expected_k,g_k)
                                                                ->
                                                                let g =
                                                                  FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k
                                                                   in
                                                                ((let uu____6961
                                                                    =
                                                                    let uu____6962
                                                                    =
                                                                    let uu____6963
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____6963
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____6962
                                                                     in
                                                                  FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____6961);
                                                                 (let act_typ3
                                                                    =
                                                                    let uu____6965
                                                                    =
                                                                    let uu____6966
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6966.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____6965
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____6991
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____6991
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____6998
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6998
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____7018
                                                                    =
                                                                    let uu____7019
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____7019]
                                                                     in
                                                                    let uu____7020
                                                                    =
                                                                    let uu____7031
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____7031]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____7018;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____7020;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____7056
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7056))
                                                                    | 
                                                                    uu____7059
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                  let uu____7061
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____7083
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____7083))
                                                                     in
                                                                  match uu____7061
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
                                                                    let uu___790_7102
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___790_7102.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___790_7102.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___790_7102.FStar_Syntax_Syntax.action_params);
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
                             match uu____5659 with
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
                                   let uu____7127 =
                                     FStar_Syntax_Subst.shift_subst
                                       (FStar_List.length ed_bs)
                                       ed_univs_closing
                                      in
                                   FStar_Syntax_Subst.subst_tscheme
                                     uu____7127 ts1
                                    in
                                 let ed3 =
                                   let uu___802_7137 = ed2  in
                                   let uu____7138 = cl signature  in
                                   let uu____7139 = cl ret_wp  in
                                   let uu____7140 = cl bind_wp  in
                                   let uu____7141 = cl stronger  in
                                   let uu____7142 =
                                     FStar_Syntax_Util.map_match_wps cl
                                       match_wps
                                      in
                                   let uu____7147 =
                                     FStar_Util.map_opt trivial cl  in
                                   let uu____7150 = cl repr  in
                                   let uu____7151 = cl return_repr  in
                                   let uu____7152 = cl bind_repr  in
                                   let uu____7153 =
                                     FStar_List.map
                                       (fun a  ->
                                          let uu___805_7161 = a  in
                                          let uu____7162 =
                                            let uu____7163 =
                                              cl
                                                ((a.FStar_Syntax_Syntax.action_univs),
                                                  (a.FStar_Syntax_Syntax.action_defn))
                                               in
                                            FStar_All.pipe_right uu____7163
                                              FStar_Pervasives_Native.snd
                                             in
                                          let uu____7188 =
                                            let uu____7189 =
                                              cl
                                                ((a.FStar_Syntax_Syntax.action_univs),
                                                  (a.FStar_Syntax_Syntax.action_typ))
                                               in
                                            FStar_All.pipe_right uu____7189
                                              FStar_Pervasives_Native.snd
                                             in
                                          {
                                            FStar_Syntax_Syntax.action_name =
                                              (uu___805_7161.FStar_Syntax_Syntax.action_name);
                                            FStar_Syntax_Syntax.action_unqualified_name
                                              =
                                              (uu___805_7161.FStar_Syntax_Syntax.action_unqualified_name);
                                            FStar_Syntax_Syntax.action_univs
                                              =
                                              (uu___805_7161.FStar_Syntax_Syntax.action_univs);
                                            FStar_Syntax_Syntax.action_params
                                              =
                                              (uu___805_7161.FStar_Syntax_Syntax.action_params);
                                            FStar_Syntax_Syntax.action_defn =
                                              uu____7162;
                                            FStar_Syntax_Syntax.action_typ =
                                              uu____7188
                                          }) actions
                                      in
                                   {
                                     FStar_Syntax_Syntax.is_layered =
                                       (uu___802_7137.FStar_Syntax_Syntax.is_layered);
                                     FStar_Syntax_Syntax.cattributes =
                                       (uu___802_7137.FStar_Syntax_Syntax.cattributes);
                                     FStar_Syntax_Syntax.mname =
                                       (uu___802_7137.FStar_Syntax_Syntax.mname);
                                     FStar_Syntax_Syntax.univs =
                                       (uu___802_7137.FStar_Syntax_Syntax.univs);
                                     FStar_Syntax_Syntax.binders =
                                       (uu___802_7137.FStar_Syntax_Syntax.binders);
                                     FStar_Syntax_Syntax.signature =
                                       uu____7138;
                                     FStar_Syntax_Syntax.ret_wp = uu____7139;
                                     FStar_Syntax_Syntax.bind_wp = uu____7140;
                                     FStar_Syntax_Syntax.stronger =
                                       uu____7141;
                                     FStar_Syntax_Syntax.match_wps =
                                       uu____7142;
                                     FStar_Syntax_Syntax.trivial = uu____7147;
                                     FStar_Syntax_Syntax.repr = uu____7150;
                                     FStar_Syntax_Syntax.return_repr =
                                       uu____7151;
                                     FStar_Syntax_Syntax.bind_repr =
                                       uu____7152;
                                     FStar_Syntax_Syntax.stronger_repr =
                                       FStar_Pervasives_Native.None;
                                     FStar_Syntax_Syntax.actions = uu____7153;
                                     FStar_Syntax_Syntax.eff_attrs =
                                       (uu___802_7137.FStar_Syntax_Syntax.eff_attrs)
                                   }  in
                                 ((let uu____7215 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "ED")
                                      in
                                   if uu____7215
                                   then
                                     let uu____7220 =
                                       FStar_Syntax_Print.eff_decl_to_string
                                         false ed3
                                        in
                                     FStar_Util.print1
                                       "Typechecked effect declaration:\n\t%s\n"
                                       uu____7220
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
        (if ed.FStar_Syntax_Syntax.is_layered
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
        let fail1 uu____7282 =
          let uu____7283 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____7289 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____7283 uu____7289  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____7333)::(wp,uu____7335)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____7364 -> fail1 ())
        | uu____7365 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____7378 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____7378
       then
         let uu____7383 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____7383
       else ());
      (let uu____7388 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____7388 with
       | (us,lift) ->
           let r = lift.FStar_Syntax_Syntax.pos  in
           let uu____7434 =
             if (FStar_List.length us) = Prims.int_zero
             then (env0, us, lift)
             else
               (let uu____7458 = FStar_Syntax_Subst.open_univ_vars us lift
                   in
                match uu____7458 with
                | (us1,lift1) ->
                    let uu____7473 =
                      FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                    (uu____7473, us1, lift1))
              in
           (match uu____7434 with
            | (env,us1,lift1) ->
                let uu____7483 =
                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                (match uu____7483 with
                 | (lift2,lc,g) ->
                     (FStar_TypeChecker_Rel.force_trivial_guard env g;
                      (let lift_ty =
                         FStar_All.pipe_right
                           lc.FStar_TypeChecker_Common.res_typ
                           (FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.Beta] env0)
                          in
                       (let uu____7496 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "LayeredEffects")
                           in
                        if uu____7496
                        then
                          let uu____7501 =
                            FStar_Syntax_Print.term_to_string lift2  in
                          let uu____7503 =
                            FStar_Syntax_Print.term_to_string lift_ty  in
                          FStar_Util.print2
                            "Typechecked lift: %s and lift_ty: %s\n"
                            uu____7501 uu____7503
                        else ());
                       (let lift_t_shape_error s =
                          let uu____7517 =
                            FStar_Ident.string_of_lid
                              sub1.FStar_Syntax_Syntax.source
                             in
                          let uu____7519 =
                            FStar_Ident.string_of_lid
                              sub1.FStar_Syntax_Syntax.target
                             in
                          let uu____7521 =
                            FStar_Syntax_Print.term_to_string lift_ty  in
                          FStar_Util.format4
                            "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                            uu____7517 uu____7519 s uu____7521
                           in
                        let uu____7524 =
                          let uu____7531 =
                            let uu____7536 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_right uu____7536
                              (fun uu____7553  ->
                                 match uu____7553 with
                                 | (t,u) ->
                                     let uu____7564 =
                                       let uu____7565 =
                                         FStar_Syntax_Syntax.gen_bv "a"
                                           FStar_Pervasives_Native.None t
                                          in
                                       FStar_All.pipe_right uu____7565
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____7564, u))
                             in
                          match uu____7531 with
                          | (a,u_a) ->
                              let rest_bs =
                                let uu____7584 =
                                  let uu____7585 =
                                    FStar_Syntax_Subst.compress lift_ty  in
                                  uu____7585.FStar_Syntax_Syntax.n  in
                                match uu____7584 with
                                | FStar_Syntax_Syntax.Tm_arrow
                                    (bs,uu____7597) when
                                    (FStar_List.length bs) >=
                                      (Prims.of_int (2))
                                    ->
                                    let uu____7625 =
                                      FStar_Syntax_Subst.open_binders bs  in
                                    (match uu____7625 with
                                     | (a',uu____7635)::bs1 ->
                                         let uu____7655 =
                                           let uu____7656 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     Prims.int_one))
                                              in
                                           FStar_All.pipe_right uu____7656
                                             FStar_Pervasives_Native.fst
                                            in
                                         let uu____7754 =
                                           let uu____7767 =
                                             let uu____7770 =
                                               let uu____7771 =
                                                 let uu____7778 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     (FStar_Pervasives_Native.fst
                                                        a)
                                                    in
                                                 (a', uu____7778)  in
                                               FStar_Syntax_Syntax.NT
                                                 uu____7771
                                                in
                                             [uu____7770]  in
                                           FStar_Syntax_Subst.subst_binders
                                             uu____7767
                                            in
                                         FStar_All.pipe_right uu____7655
                                           uu____7754)
                                | uu____7793 ->
                                    let uu____7794 =
                                      let uu____7800 =
                                        lift_t_shape_error
                                          "either not an arrow, or not enough binders"
                                         in
                                      (FStar_Errors.Fatal_UnexpectedExpressionType,
                                        uu____7800)
                                       in
                                    FStar_Errors.raise_error uu____7794 r
                                 in
                              let uu____7812 =
                                let uu____7823 =
                                  let uu____7828 =
                                    FStar_TypeChecker_Env.push_binders env (a
                                      :: rest_bs)
                                     in
                                  let uu____7835 =
                                    let uu____7836 =
                                      FStar_All.pipe_right a
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_All.pipe_right uu____7836
                                      FStar_Syntax_Syntax.bv_to_name
                                     in
                                  FStar_TypeChecker_Util.fresh_effect_repr_en
                                    uu____7828 r
                                    sub1.FStar_Syntax_Syntax.source u_a
                                    uu____7835
                                   in
                                match uu____7823 with
                                | (f_sort,g1) ->
                                    let uu____7857 =
                                      let uu____7864 =
                                        FStar_Syntax_Syntax.gen_bv "f"
                                          FStar_Pervasives_Native.None f_sort
                                         in
                                      FStar_All.pipe_right uu____7864
                                        FStar_Syntax_Syntax.mk_binder
                                       in
                                    (uu____7857, g1)
                                 in
                              (match uu____7812 with
                               | (f_b,g_f_b) ->
                                   let bs = a ::
                                     (FStar_List.append rest_bs [f_b])  in
                                   let uu____7931 =
                                     let uu____7936 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs
                                        in
                                     let uu____7937 =
                                       let uu____7938 =
                                         FStar_All.pipe_right a
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_All.pipe_right uu____7938
                                         FStar_Syntax_Syntax.bv_to_name
                                        in
                                     FStar_TypeChecker_Util.fresh_effect_repr_en
                                       uu____7936 r
                                       sub1.FStar_Syntax_Syntax.target u_a
                                       uu____7937
                                      in
                                   (match uu____7931 with
                                    | (repr,g_repr) ->
                                        let uu____7955 =
                                          let uu____7958 =
                                            let uu____7961 =
                                              let uu____7964 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  ()
                                                 in
                                              FStar_All.pipe_right uu____7964
                                                (fun _7967  ->
                                                   FStar_Pervasives_Native.Some
                                                     _7967)
                                               in
                                            FStar_Syntax_Syntax.mk_Total'
                                              repr uu____7961
                                             in
                                          FStar_Syntax_Util.arrow bs
                                            uu____7958
                                           in
                                        let uu____7968 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_f_b g_repr
                                           in
                                        (uu____7955, uu____7968)))
                           in
                        match uu____7524 with
                        | (k,g_k) ->
                            ((let uu____7978 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "LayeredEffects")
                                 in
                              if uu____7978
                              then
                                let uu____7983 =
                                  FStar_Syntax_Print.term_to_string k  in
                                FStar_Util.print1
                                  "tc_layered_lift: before unification k: %s\n"
                                  uu____7983
                              else ());
                             (let g1 =
                                FStar_TypeChecker_Rel.teq env lift_ty k  in
                              FStar_TypeChecker_Rel.force_trivial_guard env
                                g_k;
                              FStar_TypeChecker_Rel.force_trivial_guard env
                                g1;
                              (let uu____7992 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env0)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____7992
                               then
                                 let uu____7997 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "After unification k: %s\n" uu____7997
                               else ());
                              (let uu____8002 =
                                 let uu____8015 =
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 lift2
                                    in
                                 match uu____8015 with
                                 | (inst_us,lift3) ->
                                     (if
                                        (FStar_List.length inst_us) <>
                                          Prims.int_one
                                      then
                                        (let uu____8042 =
                                           let uu____8048 =
                                             let uu____8050 =
                                               FStar_Ident.string_of_lid
                                                 sub1.FStar_Syntax_Syntax.source
                                                in
                                             let uu____8052 =
                                               FStar_Ident.string_of_lid
                                                 sub1.FStar_Syntax_Syntax.target
                                                in
                                             let uu____8054 =
                                               let uu____8056 =
                                                 FStar_All.pipe_right inst_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8056
                                                 FStar_Util.string_of_int
                                                in
                                             let uu____8063 =
                                               FStar_Syntax_Print.term_to_string
                                                 lift3
                                                in
                                             FStar_Util.format4
                                               "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                               uu____8050 uu____8052
                                               uu____8054 uu____8063
                                              in
                                           (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                             uu____8048)
                                            in
                                         FStar_Errors.raise_error uu____8042
                                           r)
                                      else ();
                                      (let uu____8069 =
                                         ((FStar_List.length us1) =
                                            Prims.int_zero)
                                           ||
                                           (((FStar_List.length us1) =
                                               (FStar_List.length inst_us))
                                              &&
                                              (FStar_List.forall2
                                                 (fun u1  ->
                                                    fun u2  ->
                                                      let uu____8078 =
                                                        FStar_Syntax_Syntax.order_univ_name
                                                          u1 u2
                                                         in
                                                      uu____8078 =
                                                        Prims.int_zero) us1
                                                 inst_us))
                                          in
                                       if uu____8069
                                       then
                                         let uu____8095 =
                                           let uu____8098 =
                                             FStar_All.pipe_right k
                                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                  env)
                                              in
                                           FStar_All.pipe_right uu____8098
                                             (FStar_Syntax_Subst.close_univ_vars
                                                inst_us)
                                            in
                                         (inst_us, lift3, uu____8095)
                                       else
                                         (let uu____8109 =
                                            let uu____8115 =
                                              let uu____8117 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____8119 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____8121 =
                                                let uu____8123 =
                                                  FStar_All.pipe_right us1
                                                    FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8123
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____8130 =
                                                let uu____8132 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8132
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____8139 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format5
                                                "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                uu____8117 uu____8119
                                                uu____8121 uu____8130
                                                uu____8139
                                               in
                                            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                              uu____8115)
                                             in
                                          FStar_Errors.raise_error uu____8109
                                            r)))
                                  in
                               match uu____8002 with
                               | (us2,lift3,lift_wp) ->
                                   let sub2 =
                                     let uu___909_8171 = sub1  in
                                     {
                                       FStar_Syntax_Syntax.source =
                                         (uu___909_8171.FStar_Syntax_Syntax.source);
                                       FStar_Syntax_Syntax.target =
                                         (uu___909_8171.FStar_Syntax_Syntax.target);
                                       FStar_Syntax_Syntax.lift_wp =
                                         (FStar_Pervasives_Native.Some
                                            (us2, lift_wp));
                                       FStar_Syntax_Syntax.lift =
                                         (FStar_Pervasives_Native.Some
                                            (us2, lift3))
                                     }  in
                                   ((let uu____8181 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env0)
                                         (FStar_Options.Other
                                            "LayeredEffects")
                                        in
                                     if uu____8181
                                     then
                                       let uu____8186 =
                                         FStar_Syntax_Print.sub_eff_to_string
                                           sub2
                                          in
                                       FStar_Util.print1
                                         "Final sub_effect: %s\n" uu____8186
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
          (let uu____8212 =
             let uu____8219 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____8219
              in
           match uu____8212 with
           | (a,wp_a_src) ->
               let uu____8226 =
                 let uu____8233 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____8233
                  in
               (match uu____8226 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____8241 =
                        let uu____8244 =
                          let uu____8245 =
                            let uu____8252 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____8252)  in
                          FStar_Syntax_Syntax.NT uu____8245  in
                        [uu____8244]  in
                      FStar_Syntax_Subst.subst uu____8241 wp_b_tgt  in
                    let expected_k =
                      let uu____8260 =
                        let uu____8269 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____8276 =
                          let uu____8285 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____8285]  in
                        uu____8269 :: uu____8276  in
                      let uu____8310 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____8260 uu____8310  in
                    let repr_type eff_name a1 wp =
                      (let uu____8332 =
                         let uu____8334 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____8334  in
                       if uu____8332
                       then
                         let uu____8337 =
                           let uu____8343 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____8343)
                            in
                         let uu____8347 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____8337 uu____8347
                       else ());
                      (let uu____8350 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____8350 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ed.FStar_Syntax_Syntax.repr
                              in
                           let uu____8383 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____8384 =
                             let uu____8391 =
                               let uu____8392 =
                                 let uu____8409 =
                                   let uu____8420 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____8429 =
                                     let uu____8440 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____8440]  in
                                   uu____8420 :: uu____8429  in
                                 (repr, uu____8409)  in
                               FStar_Syntax_Syntax.Tm_app uu____8392  in
                             FStar_Syntax_Syntax.mk uu____8391  in
                           uu____8384 FStar_Pervasives_Native.None uu____8383)
                       in
                    let uu____8485 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____8658 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____8669 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____8669 with
                              | (usubst,uvs1) ->
                                  let uu____8692 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____8693 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____8692, uu____8693)
                            else (env, lift_wp)  in
                          (match uu____8658 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      tc_check_trivial_guard env1 lift_wp1
                                        expected_k
                                       in
                                    let uu____8743 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____8743))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____8814 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____8829 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____8829 with
                              | (usubst,uvs) ->
                                  let uu____8854 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____8854)
                            else ([], lift)  in
                          (match uu____8814 with
                           | (uvs,lift1) ->
                               ((let uu____8890 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____8890
                                 then
                                   let uu____8894 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____8894
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____8900 =
                                   let uu____8907 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____8907 lift1
                                    in
                                 match uu____8900 with
                                 | (lift2,comp,uu____8932) ->
                                     let uu____8933 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____8933 with
                                      | (uu____8962,lift_wp,lift_elab) ->
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
                                            let uu____8994 =
                                              let uu____9005 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____9005
                                               in
                                            let uu____9022 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____8994, uu____9022)
                                          else
                                            (let uu____9051 =
                                               let uu____9062 =
                                                 let uu____9071 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____9071)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____9062
                                                in
                                             let uu____9086 =
                                               let uu____9095 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____9095)  in
                                             (uu____9051, uu____9086))))))
                       in
                    (match uu____8485 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___989_9159 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___989_9159.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___989_9159.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___989_9159.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___989_9159.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___989_9159.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___989_9159.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___989_9159.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___989_9159.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___989_9159.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___989_9159.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___989_9159.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___989_9159.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___989_9159.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___989_9159.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___989_9159.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___989_9159.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___989_9159.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___989_9159.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___989_9159.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___989_9159.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___989_9159.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___989_9159.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___989_9159.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___989_9159.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___989_9159.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___989_9159.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___989_9159.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___989_9159.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___989_9159.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___989_9159.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___989_9159.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___989_9159.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___989_9159.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___989_9159.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___989_9159.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___989_9159.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___989_9159.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___989_9159.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___989_9159.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___989_9159.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___989_9159.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___989_9159.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___989_9159.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___989_9159.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___989_9159.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____9192 =
                                 let uu____9197 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____9197 with
                                 | (usubst,uvs1) ->
                                     let uu____9220 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____9221 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____9220, uu____9221)
                                  in
                               (match uu____9192 with
                                | (env2,lift2) ->
                                    let uu____9226 =
                                      let uu____9233 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____9233
                                       in
                                    (match uu____9226 with
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
                                             let uu____9259 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____9260 =
                                               let uu____9267 =
                                                 let uu____9268 =
                                                   let uu____9285 =
                                                     let uu____9296 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____9305 =
                                                       let uu____9316 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____9316]  in
                                                     uu____9296 :: uu____9305
                                                      in
                                                   (lift_wp1, uu____9285)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____9268
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____9267
                                                in
                                             uu____9260
                                               FStar_Pervasives_Native.None
                                               uu____9259
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____9364 =
                                             let uu____9373 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____9380 =
                                               let uu____9389 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____9396 =
                                                 let uu____9405 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____9405]  in
                                               uu____9389 :: uu____9396  in
                                             uu____9373 :: uu____9380  in
                                           let uu____9436 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow uu____9364
                                             uu____9436
                                            in
                                         let uu____9439 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____9439 with
                                          | (expected_k2,uu____9449,uu____9450)
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
                                                   let uu____9458 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____9458))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____9466 =
                             let uu____9468 =
                               let uu____9470 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____9470
                                 FStar_List.length
                                in
                             uu____9468 <> Prims.int_one  in
                           if uu____9466
                           then
                             let uu____9493 =
                               let uu____9499 =
                                 let uu____9501 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____9503 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____9505 =
                                   let uu____9507 =
                                     let uu____9509 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____9509
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____9507
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____9501 uu____9503 uu____9505
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____9499)
                                in
                             FStar_Errors.raise_error uu____9493 r
                           else ());
                          (let uu____9536 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____9539 =
                                  let uu____9541 =
                                    let uu____9544 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____9544
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____9541
                                    FStar_List.length
                                   in
                                uu____9539 <> Prims.int_one)
                              in
                           if uu____9536
                           then
                             let uu____9582 =
                               let uu____9588 =
                                 let uu____9590 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____9592 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____9594 =
                                   let uu____9596 =
                                     let uu____9598 =
                                       let uu____9601 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____9601
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____9598
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____9596
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____9590 uu____9592 uu____9594
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____9588)
                                in
                             FStar_Errors.raise_error uu____9582 r
                           else ());
                          (let uu___1026_9643 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1026_9643.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1026_9643.FStar_Syntax_Syntax.target);
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
    fun uu____9674  ->
      fun r  ->
        match uu____9674 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____9697 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____9725 = FStar_Syntax_Subst.univ_var_opening uvs  in
                 match uu____9725 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____9756 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____9756 c  in
                     let uu____9765 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____9765, uvs1, tps1, c1))
               in
            (match uu____9697 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____9785 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____9785 with
                  | (tps2,c2) ->
                      let uu____9800 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____9800 with
                       | (tps3,env3,us) ->
                           let c3 =
                             let uu____9819 =
                               (FStar_Options.use_two_phase_tc ()) &&
                                 (FStar_TypeChecker_Env.should_verify env3)
                                in
                             if uu____9819
                             then
                               let uu____9822 =
                                 FStar_TypeChecker_TcTerm.tc_comp
                                   (let uu___1056_9831 = env3  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1056_9831.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1056_9831.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1056_9831.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1056_9831.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1056_9831.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1056_9831.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1056_9831.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1056_9831.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1056_9831.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1056_9831.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1056_9831.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1056_9831.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1056_9831.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1056_9831.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1056_9831.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1056_9831.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1056_9831.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1056_9831.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1056_9831.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1056_9831.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1056_9831.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1056_9831.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1056_9831.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1056_9831.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1056_9831.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1056_9831.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1056_9831.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1056_9831.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1056_9831.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1056_9831.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1056_9831.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1056_9831.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1056_9831.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___1056_9831.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1056_9831.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___1056_9831.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1056_9831.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1056_9831.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1056_9831.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1056_9831.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1056_9831.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1056_9831.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1056_9831.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___1056_9831.FStar_TypeChecker_Env.erasable_types_tab)
                                    }) c2
                                  in
                               match uu____9822 with
                               | (c3,uu____9835,uu____9836) -> c3
                             else c2  in
                           let uu____9839 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c3  in
                           (match uu____9839 with
                            | (c4,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____9865)::uu____9866 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____9885 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c4  in
                                  let uu____9893 =
                                    let uu____9895 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____9895  in
                                  if uu____9893
                                  then
                                    let uu____9898 =
                                      let uu____9904 =
                                        let uu____9906 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____9908 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____9906 uu____9908
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____9904)
                                       in
                                    FStar_Errors.raise_error uu____9898 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c5 =
                                    FStar_Syntax_Subst.close_comp tps4 c4  in
                                  let uu____9916 =
                                    let uu____9917 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c5))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____9917
                                     in
                                  match uu____9916 with
                                  | (uvs2,t) ->
                                      let uu____9946 =
                                        let uu____9951 =
                                          let uu____9964 =
                                            let uu____9965 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____9965.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____9964)  in
                                        match uu____9951 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____9980,c6)) -> ([], c6)
                                        | (uu____10022,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c6)) -> (tps5, c6)
                                        | uu____10061 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____9946 with
                                       | (tps5,c6) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____10093 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____10093 with
                                               | (uu____10098,t1) ->
                                                   let uu____10100 =
                                                     let uu____10106 =
                                                       let uu____10108 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____10110 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____10114 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____10108
                                                         uu____10110
                                                         uu____10114
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____10106)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____10100 r)
                                            else ();
                                            (lid, uvs2, tps5, c6)))))))))
  