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
                                let x_a = fresh_x_a "x" a  in
                                let rest_bs =
                                  let uu____1180 =
                                    let uu____1181 =
                                      FStar_Syntax_Subst.compress ty  in
                                    uu____1181.FStar_Syntax_Syntax.n  in
                                  match uu____1180 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____1193) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (2))
                                      ->
                                      let uu____1221 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____1221 with
                                       | (a',uu____1231)::(x',uu____1233)::bs1
                                           ->
                                           let uu____1263 =
                                             let uu____1264 =
                                               let uu____1269 =
                                                 let uu____1272 =
                                                   let uu____1273 =
                                                     let uu____1280 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a', uu____1280)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____1273
                                                    in
                                                 [uu____1272]  in
                                               FStar_Syntax_Subst.subst_binders
                                                 uu____1269
                                                in
                                             FStar_All.pipe_right bs1
                                               uu____1264
                                              in
                                           let uu____1287 =
                                             let uu____1300 =
                                               let uu____1303 =
                                                 let uu____1304 =
                                                   let uu____1311 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       (FStar_Pervasives_Native.fst
                                                          x_a)
                                                      in
                                                   (x', uu____1311)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____1304
                                                  in
                                               [uu____1303]  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____1300
                                              in
                                           FStar_All.pipe_right uu____1263
                                             uu____1287)
                                  | uu____1326 ->
                                      not_an_arrow_error "return"
                                        (Prims.of_int (2)) ty r
                                   in
                                let bs = a :: x_a :: rest_bs  in
                                let uu____1350 =
                                  let uu____1355 =
                                    FStar_TypeChecker_Env.push_binders env bs
                                     in
                                  let uu____1356 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst a)
                                      FStar_Syntax_Syntax.bv_to_name
                                     in
                                  fresh_repr r uu____1355 u_a uu____1356  in
                                (match uu____1350 with
                                 | (repr1,g) ->
                                     let k =
                                       let uu____1376 =
                                         FStar_Syntax_Syntax.mk_Total' repr1
                                           (FStar_Pervasives_Native.Some u_a)
                                          in
                                       FStar_Syntax_Util.arrow bs uu____1376
                                        in
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env ty k  in
                                     ((let uu____1381 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           g_eq
                                          in
                                       FStar_TypeChecker_Rel.force_trivial_guard
                                         env uu____1381);
                                      (let uu____1382 =
                                         let uu____1385 =
                                           FStar_All.pipe_right k
                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                env)
                                            in
                                         FStar_Syntax_Subst.close_univ_vars
                                           us uu____1385
                                          in
                                       (ret_us, ret_t, uu____1382))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let bind_repr_ts =
                     let uu____1412 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_bind_repr
                        in
                     FStar_All.pipe_right uu____1412 FStar_Util.must  in
                   let r =
                     (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
                      in
                   let uu____1424 =
                     check_and_gen "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1424 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1448 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1448 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            let uu____1468 = fresh_a_and_u_a "a"  in
                            (match uu____1468 with
                             | (a,u_a) ->
                                 let uu____1488 = fresh_a_and_u_a "b"  in
                                 (match uu____1488 with
                                  | (b,u_b) ->
                                      let rest_bs =
                                        let uu____1517 =
                                          let uu____1518 =
                                            FStar_Syntax_Subst.compress ty
                                             in
                                          uu____1518.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1517 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs,uu____1530) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (4))
                                            ->
                                            let uu____1558 =
                                              FStar_Syntax_Subst.open_binders
                                                bs
                                               in
                                            (match uu____1558 with
                                             | (a',uu____1568)::(b',uu____1570)::bs1
                                                 ->
                                                 let uu____1600 =
                                                   let uu____1601 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             -
                                                             (Prims.of_int (2))))
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____1601
                                                     FStar_Pervasives_Native.fst
                                                    in
                                                 let uu____1699 =
                                                   let uu____1712 =
                                                     let uu____1715 =
                                                       let uu____1716 =
                                                         let uu____1723 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                a)
                                                            in
                                                         (a', uu____1723)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____1716
                                                        in
                                                     let uu____1730 =
                                                       let uu____1733 =
                                                         let uu____1734 =
                                                           let uu____1741 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               (FStar_Pervasives_Native.fst
                                                                  b)
                                                              in
                                                           (b', uu____1741)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____1734
                                                          in
                                                       [uu____1733]  in
                                                     uu____1715 :: uu____1730
                                                      in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____1712
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____1600 uu____1699)
                                        | uu____1756 ->
                                            not_an_arrow_error "bind"
                                              (Prims.of_int (4)) ty r
                                         in
                                      let bs = a :: b :: rest_bs  in
                                      let uu____1780 =
                                        let uu____1791 =
                                          let uu____1796 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____1797 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____1796 u_a
                                            uu____1797
                                           in
                                        match uu____1791 with
                                        | (repr1,g) ->
                                            let uu____1812 =
                                              let uu____1819 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1
                                                 in
                                              FStar_All.pipe_right uu____1819
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            (uu____1812, g)
                                         in
                                      (match uu____1780 with
                                       | (f,guard_f) ->
                                           let uu____1859 =
                                             let x_a = fresh_x_a "x" a  in
                                             let uu____1872 =
                                               let uu____1877 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env
                                                   (FStar_List.append bs
                                                      [x_a])
                                                  in
                                               let uu____1896 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.fst
                                                      b)
                                                   FStar_Syntax_Syntax.bv_to_name
                                                  in
                                               fresh_repr r uu____1877 u_b
                                                 uu____1896
                                                in
                                             match uu____1872 with
                                             | (repr1,g) ->
                                                 let uu____1911 =
                                                   let uu____1918 =
                                                     let uu____1919 =
                                                       let uu____1920 =
                                                         let uu____1923 =
                                                           let uu____1926 =
                                                             FStar_TypeChecker_Env.new_u_univ
                                                               ()
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1926
                                                            in
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1 uu____1923
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         [x_a] uu____1920
                                                        in
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "g"
                                                       FStar_Pervasives_Native.None
                                                       uu____1919
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____1918
                                                     FStar_Syntax_Syntax.mk_binder
                                                    in
                                                 (uu____1911, g)
                                              in
                                           (match uu____1859 with
                                            | (g,guard_g) ->
                                                let uu____1978 =
                                                  let uu____1983 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____1984 =
                                                    FStar_All.pipe_right
                                                      (FStar_Pervasives_Native.fst
                                                         b)
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____1983 u_b
                                                    uu____1984
                                                   in
                                                (match uu____1978 with
                                                 | (repr1,guard_repr) ->
                                                     let k =
                                                       let uu____2004 =
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1
                                                           (FStar_Pervasives_Native.Some
                                                              u_b)
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         (FStar_List.append
                                                            bs [f; g])
                                                         uu____2004
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
                                                      (let uu____2033 =
                                                         let uu____2036 =
                                                           FStar_All.pipe_right
                                                             k
                                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                env)
                                                            in
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           bind_us uu____2036
                                                          in
                                                       (bind_us, bind_t,
                                                         uu____2033)))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2063 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2063 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2091 =
                      check_and_gen "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2091 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2116 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2116
                          then
                            let uu____2121 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2127 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2121 uu____2127
                          else ());
                         (let uu____2136 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2136 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              let uu____2156 = fresh_a_and_u_a "a"  in
                              (match uu____2156 with
                               | (a,u) ->
                                   let rest_bs =
                                     let uu____2185 =
                                       let uu____2186 =
                                         FStar_Syntax_Subst.compress ty  in
                                       uu____2186.FStar_Syntax_Syntax.n  in
                                     match uu____2185 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (bs,uu____2198) when
                                         (FStar_List.length bs) >=
                                           (Prims.of_int (2))
                                         ->
                                         let uu____2226 =
                                           FStar_Syntax_Subst.open_binders bs
                                            in
                                         (match uu____2226 with
                                          | (a',uu____2236)::bs1 ->
                                              let uu____2256 =
                                                let uu____2257 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.splitAt
                                                       ((FStar_List.length
                                                           bs1)
                                                          - Prims.int_one))
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2257
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              let uu____2355 =
                                                let uu____2368 =
                                                  let uu____2371 =
                                                    let uu____2372 =
                                                      let uu____2379 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____2379)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____2372
                                                     in
                                                  [uu____2371]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____2368
                                                 in
                                              FStar_All.pipe_right uu____2256
                                                uu____2355)
                                     | uu____2394 ->
                                         not_an_arrow_error "stronger"
                                           (Prims.of_int (2)) ty r
                                      in
                                   let bs = a :: rest_bs  in
                                   let uu____2412 =
                                     let uu____2423 =
                                       let uu____2428 =
                                         FStar_TypeChecker_Env.push_binders
                                           env bs
                                          in
                                       let uu____2429 =
                                         FStar_All.pipe_right
                                           (FStar_Pervasives_Native.fst a)
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       fresh_repr r uu____2428 u uu____2429
                                        in
                                     match uu____2423 with
                                     | (repr1,g) ->
                                         let uu____2444 =
                                           let uu____2451 =
                                             FStar_Syntax_Syntax.gen_bv "f"
                                               FStar_Pervasives_Native.None
                                               repr1
                                              in
                                           FStar_All.pipe_right uu____2451
                                             FStar_Syntax_Syntax.mk_binder
                                            in
                                         (uu____2444, g)
                                      in
                                   (match uu____2412 with
                                    | (f,guard_f) ->
                                        let uu____2491 =
                                          let uu____2496 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____2497 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____2496 u
                                            uu____2497
                                           in
                                        (match uu____2491 with
                                         | (ret_t,guard_ret_t) ->
                                             let pure_wp_t =
                                               let pure_wp_ts =
                                                 let uu____2516 =
                                                   FStar_TypeChecker_Env.lookup_definition
                                                     [FStar_TypeChecker_Env.NoDelta]
                                                     env
                                                     FStar_Parser_Const.pure_wp_lid
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2516 FStar_Util.must
                                                  in
                                               let uu____2533 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   pure_wp_ts
                                                  in
                                               match uu____2533 with
                                               | (uu____2538,pure_wp_t) ->
                                                   let uu____2540 =
                                                     let uu____2545 =
                                                       let uu____2546 =
                                                         FStar_All.pipe_right
                                                           ret_t
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____2546]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       pure_wp_t uu____2545
                                                      in
                                                   uu____2540
                                                     FStar_Pervasives_Native.None
                                                     r
                                                in
                                             let uu____2579 =
                                               let reason =
                                                 FStar_Util.format1
                                                   "implicit for pure_wp in checking stronger for %s"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                  in
                                               let uu____2595 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs
                                                  in
                                               FStar_TypeChecker_Util.new_implicit_var
                                                 reason r uu____2595
                                                 pure_wp_t
                                                in
                                             (match uu____2579 with
                                              | (pure_wp_uvar,uu____2609,guard_wp)
                                                  ->
                                                  let c =
                                                    let uu____2624 =
                                                      let uu____2625 =
                                                        let uu____2626 =
                                                          FStar_TypeChecker_Env.new_u_univ
                                                            ()
                                                           in
                                                        [uu____2626]  in
                                                      let uu____2627 =
                                                        let uu____2638 =
                                                          FStar_All.pipe_right
                                                            pure_wp_uvar
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____2638]  in
                                                      {
                                                        FStar_Syntax_Syntax.comp_univs
                                                          = uu____2625;
                                                        FStar_Syntax_Syntax.effect_name
                                                          =
                                                          FStar_Parser_Const.effect_PURE_lid;
                                                        FStar_Syntax_Syntax.result_typ
                                                          = ret_t;
                                                        FStar_Syntax_Syntax.effect_args
                                                          = uu____2627;
                                                        FStar_Syntax_Syntax.flags
                                                          = []
                                                      }  in
                                                    FStar_Syntax_Syntax.mk_Comp
                                                      uu____2624
                                                     in
                                                  let k =
                                                    FStar_Syntax_Util.arrow
                                                      (FStar_List.append bs
                                                         [f]) c
                                                     in
                                                  ((let uu____2693 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "LayeredEffects")
                                                       in
                                                    if uu____2693
                                                    then
                                                      let uu____2698 =
                                                        FStar_Syntax_Print.term_to_string
                                                          k
                                                         in
                                                      FStar_Util.print1
                                                        "Expected type before unification: %s\n"
                                                        uu____2698
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
                                                     let uu____2706 =
                                                       let uu____2709 =
                                                         FStar_All.pipe_right
                                                           k1
                                                           (FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Env.Beta;
                                                              FStar_TypeChecker_Env.Eager_unfolding]
                                                              env)
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____2709
                                                         (FStar_Syntax_Subst.close_univ_vars
                                                            stronger_us)
                                                        in
                                                     (stronger_us,
                                                       stronger_t,
                                                       uu____2706))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2738 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2738 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2766 =
                       check_and_gen "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2766 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2790 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2790 with
                          | (us,t) ->
                              let uu____2809 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2809 with
                               | (uu____2826,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   let uu____2829 = fresh_a_and_u_a "a"  in
                                   (match uu____2829 with
                                    | (a,u_a) ->
                                        let rest_bs =
                                          let uu____2858 =
                                            let uu____2859 =
                                              FStar_Syntax_Subst.compress ty
                                               in
                                            uu____2859.FStar_Syntax_Syntax.n
                                             in
                                          match uu____2858 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,uu____2871) when
                                              (FStar_List.length bs) >=
                                                (Prims.of_int (4))
                                              ->
                                              let uu____2899 =
                                                FStar_Syntax_Subst.open_binders
                                                  bs
                                                 in
                                              (match uu____2899 with
                                               | (a',uu____2909)::bs1 ->
                                                   let uu____2929 =
                                                     let uu____2930 =
                                                       FStar_All.pipe_right
                                                         bs1
                                                         (FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs1)
                                                               -
                                                               (Prims.of_int (3))))
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____2930
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____3028 =
                                                     let uu____3041 =
                                                       let uu____3044 =
                                                         let uu____3045 =
                                                           let uu____3052 =
                                                             let uu____3055 =
                                                               FStar_All.pipe_right
                                                                 a
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____3055
                                                               FStar_Syntax_Syntax.bv_to_name
                                                              in
                                                           (a', uu____3052)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____3045
                                                          in
                                                       [uu____3044]  in
                                                     FStar_Syntax_Subst.subst_binders
                                                       uu____3041
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____2929 uu____3028)
                                          | uu____3076 ->
                                              not_an_arrow_error
                                                "if_then_else"
                                                (Prims.of_int (4)) ty r
                                           in
                                        let bs = a :: rest_bs  in
                                        let uu____3094 =
                                          let uu____3105 =
                                            let uu____3110 =
                                              FStar_TypeChecker_Env.push_binders
                                                env bs
                                               in
                                            let uu____3111 =
                                              let uu____3112 =
                                                FStar_All.pipe_right a
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right uu____3112
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            fresh_repr r uu____3110 u_a
                                              uu____3111
                                             in
                                          match uu____3105 with
                                          | (repr1,g) ->
                                              let uu____3133 =
                                                let uu____3140 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "f"
                                                    FStar_Pervasives_Native.None
                                                    repr1
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3140
                                                  FStar_Syntax_Syntax.mk_binder
                                                 in
                                              (uu____3133, g)
                                           in
                                        (match uu____3094 with
                                         | (f_bs,guard_f) ->
                                             let uu____3180 =
                                               let uu____3191 =
                                                 let uu____3196 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env bs
                                                    in
                                                 let uu____3197 =
                                                   let uu____3198 =
                                                     FStar_All.pipe_right a
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3198
                                                     FStar_Syntax_Syntax.bv_to_name
                                                    in
                                                 fresh_repr r uu____3196 u_a
                                                   uu____3197
                                                  in
                                               match uu____3191 with
                                               | (repr1,g) ->
                                                   let uu____3219 =
                                                     let uu____3226 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "g"
                                                         FStar_Pervasives_Native.None
                                                         repr1
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3226
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   (uu____3219, g)
                                                in
                                             (match uu____3180 with
                                              | (g_bs,guard_g) ->
                                                  let p_b =
                                                    let uu____3273 =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "p"
                                                        FStar_Pervasives_Native.None
                                                        FStar_Syntax_Util.ktype0
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3273
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  let uu____3281 =
                                                    let uu____3286 =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env
                                                        (FStar_List.append bs
                                                           [p_b])
                                                       in
                                                    let uu____3305 =
                                                      let uu____3306 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3306
                                                        FStar_Syntax_Syntax.bv_to_name
                                                       in
                                                    fresh_repr r uu____3286
                                                      u_a uu____3305
                                                     in
                                                  (match uu____3281 with
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
                                                        (let uu____3366 =
                                                           let uu____3369 =
                                                             FStar_All.pipe_right
                                                               k
                                                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                  env)
                                                              in
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             if_then_else_us
                                                             uu____3369
                                                            in
                                                         (if_then_else_us,
                                                           uu____3366,
                                                           if_then_else_ty)))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3380 =
                        let uu____3383 =
                          let uu____3392 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3392 FStar_Util.must  in
                        FStar_All.pipe_right uu____3383
                          FStar_Pervasives_Native.snd
                         in
                      uu____3380.FStar_Syntax_Syntax.pos  in
                    let uu____3421 = if_then_else1  in
                    match uu____3421 with
                    | (ite_us,ite_t,uu____3436) ->
                        let uu____3449 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3449 with
                         | (us,ite_t1) ->
                             let uu____3456 =
                               let uu____3467 =
                                 let uu____3468 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3468.FStar_Syntax_Syntax.n  in
                               match uu____3467 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3482,uu____3483) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3509 =
                                     let uu____3516 =
                                       let uu____3519 =
                                         let uu____3522 =
                                           let uu____3531 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3531
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3522
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3519
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3516
                                       (fun l  ->
                                          let uu____3675 = l  in
                                          match uu____3675 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3509 with
                                    | (f,g,p) ->
                                        let uu____3700 =
                                          let uu____3701 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3701 bs1
                                           in
                                        let uu____3702 =
                                          let uu____3703 =
                                            let uu____3708 =
                                              let uu____3709 =
                                                let uu____3712 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3712
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____3709
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____3708
                                             in
                                          uu____3703
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____3700, uu____3702, f, g, p))
                               | uu____3739 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3456 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____3756 =
                                    let uu____3765 = stronger_repr  in
                                    match uu____3765 with
                                    | (uu____3786,subcomp_t,subcomp_ty) ->
                                        let uu____3801 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3801 with
                                         | (uu____3814,subcomp_t1) ->
                                             let bs_except_last =
                                               let uu____3825 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____3825 with
                                               | (uu____3838,subcomp_ty1) ->
                                                   let uu____3840 =
                                                     let uu____3841 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____3841.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____3840 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____3853) ->
                                                        let uu____3874 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3874
                                                          FStar_Pervasives_Native.fst
                                                    | uu____3980 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             let aux t =
                                               let uu____3998 =
                                                 let uu____4003 =
                                                   let uu____4004 =
                                                     let uu____4007 =
                                                       FStar_All.pipe_right
                                                         bs_except_last
                                                         (FStar_List.map
                                                            (fun uu____4027 
                                                               ->
                                                               FStar_Syntax_Syntax.tun))
                                                        in
                                                     FStar_List.append
                                                       uu____4007 [t]
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____4004
                                                     (FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg)
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   subcomp_t1 uu____4003
                                                  in
                                               uu____3998
                                                 FStar_Pervasives_Native.None
                                                 r
                                                in
                                             let uu____4036 = aux f_t  in
                                             let uu____4039 = aux g_t  in
                                             (uu____4036, uu____4039))
                                     in
                                  (match uu____3756 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4056 =
                                         let aux t =
                                           let uu____4073 =
                                             let uu____4080 =
                                               let uu____4081 =
                                                 let uu____4108 =
                                                   let uu____4125 =
                                                     let uu____4134 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4134
                                                      in
                                                   (uu____4125,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4108,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4081
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4080
                                              in
                                           uu____4073
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4175 = aux subcomp_f  in
                                         let uu____4176 = aux subcomp_g  in
                                         (uu____4175, uu____4176)  in
                                       (match uu____4056 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4180 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4180
                                              then
                                                let uu____4185 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4187 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4185 uu____4187
                                              else ());
                                             (let uu____4192 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4192 with
                                              | (uu____4199,uu____4200,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4203 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4203 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4205 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4205 with
                                                    | (uu____4212,uu____4213,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4219 =
                                                              let uu____4224
                                                                =
                                                                let uu____4225
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4225
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4226
                                                                =
                                                                let uu____4227
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4227]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4224
                                                                uu____4226
                                                               in
                                                            uu____4219
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4260 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4260 g_g
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
                        (let uu____4284 =
                           let uu____4290 =
                             let uu____4292 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4292
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4290)
                            in
                         FStar_Errors.raise_error uu____4284 r)
                      else ();
                      (let uu____4299 =
                         let uu____4304 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4304 with
                         | (usubst,us) ->
                             let uu____4327 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4328 =
                               let uu___418_4329 = act  in
                               let uu____4330 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4331 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___418_4329.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___418_4329.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___418_4329.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4330;
                                 FStar_Syntax_Syntax.action_typ = uu____4331
                               }  in
                             (uu____4327, uu____4328)
                          in
                       match uu____4299 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4335 =
                               let uu____4336 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4336.FStar_Syntax_Syntax.n  in
                             match uu____4335 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4362 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4362
                                 then
                                   let repr_ts =
                                     let uu____4366 = repr  in
                                     match uu____4366 with
                                     | (us,t,uu____4381) -> (us, t)  in
                                   let repr1 =
                                     let uu____4399 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4399
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4411 =
                                       let uu____4416 =
                                         let uu____4417 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4417 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4416
                                        in
                                     uu____4411 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4435 =
                                       let uu____4438 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4438
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4435
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4441 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4442 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4442 with
                            | (act_typ1,uu____4450,g_t) ->
                                let uu____4452 =
                                  let uu____4459 =
                                    let uu___443_4460 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___443_4460.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___443_4460.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___443_4460.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___443_4460.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___443_4460.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___443_4460.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___443_4460.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___443_4460.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___443_4460.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___443_4460.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___443_4460.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___443_4460.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___443_4460.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___443_4460.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___443_4460.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___443_4460.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___443_4460.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___443_4460.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___443_4460.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___443_4460.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___443_4460.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___443_4460.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___443_4460.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___443_4460.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___443_4460.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___443_4460.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___443_4460.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___443_4460.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___443_4460.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___443_4460.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___443_4460.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___443_4460.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___443_4460.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___443_4460.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___443_4460.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___443_4460.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___443_4460.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___443_4460.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___443_4460.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___443_4460.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___443_4460.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___443_4460.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___443_4460.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___443_4460.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4459
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4452 with
                                 | (act_defn,uu____4463,g_d) ->
                                     ((let uu____4466 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4466
                                       then
                                         let uu____4471 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4473 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4471 uu____4473
                                       else ());
                                      (let uu____4478 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4486 =
                                           let uu____4487 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4487.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4486 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4497) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4520 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4520 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4536 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4536 with
                                                   | (a_tm,uu____4556,g_tm)
                                                       ->
                                                       let uu____4570 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4570 with
                                                        | (repr1,g) ->
                                                            let uu____4583 =
                                                              let uu____4586
                                                                =
                                                                let uu____4589
                                                                  =
                                                                  let uu____4592
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4592
                                                                    (
                                                                    fun _4595
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4595)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4589
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4586
                                                               in
                                                            let uu____4596 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4583,
                                                              uu____4596))))
                                         | uu____4599 ->
                                             let uu____4600 =
                                               let uu____4606 =
                                                 let uu____4608 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____4608
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4606)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4600 r
                                          in
                                       match uu____4478 with
                                       | (k,g_k) ->
                                           ((let uu____4625 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4625
                                             then
                                               let uu____4630 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4630
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4638 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4638
                                              then
                                                let uu____4643 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4643
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4656 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____4656
                                                   in
                                                let repr_args t =
                                                  let uu____4677 =
                                                    let uu____4678 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4678.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4677 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4730 =
                                                        let uu____4731 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4731.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4730 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4740,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4750 ->
                                                           let uu____4751 =
                                                             let uu____4757 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4757)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4751 r)
                                                  | uu____4766 ->
                                                      let uu____4767 =
                                                        let uu____4773 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4773)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4767 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4783 =
                                                  let uu____4784 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4784.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4783 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4809 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4809 with
                                                     | (bs1,c1) ->
                                                         let uu____4816 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____4816
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
                                                              let uu____4827
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4827))
                                                | uu____4830 ->
                                                    let uu____4831 =
                                                      let uu____4837 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____4837)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____4831 r
                                                 in
                                              (let uu____4841 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____4841
                                               then
                                                 let uu____4846 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____4846
                                               else ());
                                              (let act2 =
                                                 let uu____4852 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____4852 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___516_4866 =
                                                         act1  in
                                                       let uu____4867 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___516_4866.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___516_4866.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___516_4866.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____4867
                                                       }
                                                     else
                                                       (let uu____4870 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____4877
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____4877
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____4870
                                                        then
                                                          let uu___521_4882 =
                                                            act1  in
                                                          let uu____4883 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___521_4882.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___521_4882.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___521_4882.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___521_4882.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____4883
                                                          }
                                                        else
                                                          (let uu____4886 =
                                                             let uu____4892 =
                                                               let uu____4894
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____4896
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____4894
                                                                 uu____4896
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____4892)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4886 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____4921 =
                      match uu____4921 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____4966 =
                        let uu____4967 = tschemes_of repr  in
                        let uu____4972 = tschemes_of return_repr  in
                        let uu____4977 = tschemes_of bind_repr  in
                        let uu____4982 = tschemes_of stronger_repr  in
                        let uu____4987 = tschemes_of if_then_else1  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____4967;
                          FStar_Syntax_Syntax.l_return = uu____4972;
                          FStar_Syntax_Syntax.l_bind = uu____4977;
                          FStar_Syntax_Syntax.l_subcomp = uu____4982;
                          FStar_Syntax_Syntax.l_if_then_else = uu____4987
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____4966  in
                    let uu___530_4992 = ed  in
                    let uu____4993 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___530_4992.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___530_4992.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___530_4992.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___530_4992.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5000 = signature  in
                         match uu____5000 with | (us,t,uu____5015) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____4993;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___530_4992.FStar_Syntax_Syntax.eff_attrs)
                    }))))))))
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____5048 =
          FStar_TypeChecker_TcTerm.tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____5048
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____5070 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5070
         then
           let uu____5075 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5075
         else ());
        (let uu____5081 =
           let uu____5086 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5086 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5110 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5110  in
               let uu____5111 =
                 let uu____5118 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5118 bs  in
               (match uu____5111 with
                | (bs1,uu____5124,uu____5125) ->
                    let uu____5126 =
                      let tmp_t =
                        let uu____5136 =
                          let uu____5139 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5144  ->
                                 FStar_Pervasives_Native.Some _5144)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5139
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5136  in
                      let uu____5145 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5145 with
                      | (us,tmp_t1) ->
                          let uu____5162 =
                            let uu____5163 =
                              let uu____5164 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5164
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5163
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5162)
                       in
                    (match uu____5126 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5201 ->
                              let uu____5204 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5211 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5211 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5204
                              then (us, bs2)
                              else
                                (let uu____5222 =
                                   let uu____5228 =
                                     let uu____5230 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5232 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5230 uu____5232
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5228)
                                    in
                                 let uu____5236 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5222
                                   uu____5236))))
            in
         match uu____5081 with
         | (us,bs) ->
             let ed1 =
               let uu___567_5244 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___567_5244.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___567_5244.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___567_5244.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___567_5244.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___567_5244.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___567_5244.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5245 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5245 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5264 =
                    let uu____5269 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5269  in
                  (match uu____5264 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5290 =
                           match uu____5290 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5310 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5310 t  in
                               let uu____5319 =
                                 let uu____5320 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5320 t1  in
                               (us1, uu____5319)
                            in
                         let uu___581_5325 = ed1  in
                         let uu____5326 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5327 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5328 =
                           FStar_List.map
                             (fun a  ->
                                let uu___584_5336 = a  in
                                let uu____5337 =
                                  let uu____5338 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5338  in
                                let uu____5349 =
                                  let uu____5350 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5350  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___584_5336.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___584_5336.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___584_5336.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___584_5336.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5337;
                                  FStar_Syntax_Syntax.action_typ = uu____5349
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___581_5325.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___581_5325.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___581_5325.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___581_5325.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5326;
                           FStar_Syntax_Syntax.combinators = uu____5327;
                           FStar_Syntax_Syntax.actions = uu____5328;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___581_5325.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5362 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5362
                         then
                           let uu____5367 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5367
                         else ());
                        (let env =
                           let uu____5374 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5374
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5409 k =
                           match uu____5409 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5429 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5429 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5438 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5438 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5439 =
                                            let uu____5446 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5446 t1
                                             in
                                          (match uu____5439 with
                                           | (t2,uu____5448,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5451 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5451 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5467 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5469 =
                                                 let uu____5471 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5471
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5467 uu____5469
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5486 ->
                                               let uu____5487 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5494 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5494 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5487
                                               then (g_us, t3)
                                               else
                                                 (let uu____5505 =
                                                    let uu____5511 =
                                                      let uu____5513 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5515 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5513
                                                        uu____5515
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5511)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5505
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5523 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5523
                          then
                            let uu____5528 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5528
                          else ());
                         (let fresh_a_and_wp uu____5544 =
                            let fail1 t =
                              let uu____5557 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5557
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5573 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5573 with
                            | (uu____5584,signature1) ->
                                let uu____5586 =
                                  let uu____5587 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5587.FStar_Syntax_Syntax.n  in
                                (match uu____5586 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5597) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5626)::(wp,uu____5628)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5657 -> fail1 signature1)
                                 | uu____5658 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5672 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5672
                            then
                              let uu____5677 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____5677
                            else ()  in
                          let ret_wp =
                            let uu____5683 = fresh_a_and_wp ()  in
                            match uu____5683 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5699 =
                                    let uu____5708 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5715 =
                                      let uu____5724 =
                                        let uu____5731 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5731
                                         in
                                      [uu____5724]  in
                                    uu____5708 :: uu____5715  in
                                  let uu____5750 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5699
                                    uu____5750
                                   in
                                let uu____5753 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____5753
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5767 = fresh_a_and_wp ()  in
                             match uu____5767 with
                             | (a,wp_sort_a) ->
                                 let uu____5780 = fresh_a_and_wp ()  in
                                 (match uu____5780 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5796 =
                                          let uu____5805 =
                                            let uu____5812 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5812
                                             in
                                          [uu____5805]  in
                                        let uu____5825 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5796
                                          uu____5825
                                         in
                                      let k =
                                        let uu____5831 =
                                          let uu____5840 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5847 =
                                            let uu____5856 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5863 =
                                              let uu____5872 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____5879 =
                                                let uu____5888 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____5895 =
                                                  let uu____5904 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____5904]  in
                                                uu____5888 :: uu____5895  in
                                              uu____5872 :: uu____5879  in
                                            uu____5856 :: uu____5863  in
                                          uu____5840 :: uu____5847  in
                                        let uu____5947 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5831
                                          uu____5947
                                         in
                                      let uu____5950 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____5950
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____5964 = fresh_a_and_wp ()  in
                              match uu____5964 with
                              | (a,wp_sort_a) ->
                                  let uu____5977 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____5977 with
                                   | (t,uu____5983) ->
                                       let k =
                                         let uu____5987 =
                                           let uu____5996 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6003 =
                                             let uu____6012 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6019 =
                                               let uu____6028 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6028]  in
                                             uu____6012 :: uu____6019  in
                                           uu____5996 :: uu____6003  in
                                         let uu____6059 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____5987
                                           uu____6059
                                          in
                                       let uu____6062 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6062
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else1 =
                               let uu____6076 = fresh_a_and_wp ()  in
                               match uu____6076 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6090 =
                                       let uu____6093 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6093
                                        in
                                     let uu____6094 =
                                       let uu____6095 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6095
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6090
                                       uu____6094
                                      in
                                   let k =
                                     let uu____6107 =
                                       let uu____6116 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6123 =
                                         let uu____6132 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6139 =
                                           let uu____6148 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6155 =
                                             let uu____6164 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6164]  in
                                           uu____6148 :: uu____6155  in
                                         uu____6132 :: uu____6139  in
                                       uu____6116 :: uu____6123  in
                                     let uu____6201 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6107
                                       uu____6201
                                      in
                                   let uu____6204 =
                                     let uu____6209 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6209
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6204
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else1;
                             (let ite_wp =
                                let uu____6241 = fresh_a_and_wp ()  in
                                match uu____6241 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6257 =
                                        let uu____6266 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6273 =
                                          let uu____6282 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6282]  in
                                        uu____6266 :: uu____6273  in
                                      let uu____6307 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6257
                                        uu____6307
                                       in
                                    let uu____6310 =
                                      let uu____6315 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6315
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6310
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6331 = fresh_a_and_wp ()  in
                                 match uu____6331 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6345 =
                                         let uu____6348 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6348
                                          in
                                       let uu____6349 =
                                         let uu____6350 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6350
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6345
                                         uu____6349
                                        in
                                     let wp_sort_b_a =
                                       let uu____6362 =
                                         let uu____6371 =
                                           let uu____6378 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6378
                                            in
                                         [uu____6371]  in
                                       let uu____6391 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6362
                                         uu____6391
                                        in
                                     let k =
                                       let uu____6397 =
                                         let uu____6406 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6413 =
                                           let uu____6422 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6429 =
                                             let uu____6438 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6438]  in
                                           uu____6422 :: uu____6429  in
                                         uu____6406 :: uu____6413  in
                                       let uu____6469 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6397
                                         uu____6469
                                        in
                                     let uu____6472 =
                                       let uu____6477 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6477
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6472
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6493 = fresh_a_and_wp ()  in
                                  match uu____6493 with
                                  | (a,wp_sort_a) ->
                                      let uu____6506 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6506 with
                                       | (t,uu____6512) ->
                                           let k =
                                             let uu____6516 =
                                               let uu____6525 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6532 =
                                                 let uu____6541 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6541]  in
                                               uu____6525 :: uu____6532  in
                                             let uu____6566 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6516 uu____6566
                                              in
                                           let trivial =
                                             let uu____6570 =
                                               let uu____6575 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6575 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6570
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____6590 =
                                  let uu____6607 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____6607 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6636 ->
                                      let repr =
                                        let uu____6640 = fresh_a_and_wp ()
                                           in
                                        match uu____6640 with
                                        | (a,wp_sort_a) ->
                                            let uu____6653 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____6653 with
                                             | (t,uu____6659) ->
                                                 let k =
                                                   let uu____6663 =
                                                     let uu____6672 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6679 =
                                                       let uu____6688 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____6688]  in
                                                     uu____6672 :: uu____6679
                                                      in
                                                   let uu____6713 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6663 uu____6713
                                                    in
                                                 let uu____6716 =
                                                   let uu____6721 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6721
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____6716
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____6765 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____6765 with
                                          | (uu____6772,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____6775 =
                                                let uu____6782 =
                                                  let uu____6783 =
                                                    let uu____6800 =
                                                      let uu____6811 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____6828 =
                                                        let uu____6839 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____6839]  in
                                                      uu____6811 ::
                                                        uu____6828
                                                       in
                                                    (repr2, uu____6800)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6783
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____6782
                                                 in
                                              uu____6775
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____6905 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____6905 wp  in
                                        let destruct_repr t =
                                          let uu____6920 =
                                            let uu____6921 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____6921.FStar_Syntax_Syntax.n
                                             in
                                          match uu____6920 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____6932,(t1,uu____6934)::
                                               (wp,uu____6936)::[])
                                              -> (t1, wp)
                                          | uu____6995 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7011 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7011
                                              FStar_Util.must
                                             in
                                          let uu____7038 = fresh_a_and_wp ()
                                             in
                                          match uu____7038 with
                                          | (a,uu____7046) ->
                                              let x_a =
                                                let uu____7052 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7052
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7060 =
                                                    let uu____7065 =
                                                      let uu____7066 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7066
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____7075 =
                                                      let uu____7076 =
                                                        let uu____7085 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7085
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7094 =
                                                        let uu____7105 =
                                                          let uu____7114 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7114
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7105]  in
                                                      uu____7076 ::
                                                        uu____7094
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____7065 uu____7075
                                                     in
                                                  uu____7060
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7150 =
                                                  let uu____7159 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7166 =
                                                    let uu____7175 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7175]  in
                                                  uu____7159 :: uu____7166
                                                   in
                                                let uu____7200 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7150 uu____7200
                                                 in
                                              let uu____7203 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7203 with
                                               | (k1,uu____7211,uu____7212)
                                                   ->
                                                   let env1 =
                                                     let uu____7216 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7216
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
                                             let uu____7229 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7229
                                               FStar_Util.must
                                              in
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
                                                          uu____7344
                                                          uu____7345
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
                                                              let uu____7405
                                                                =
                                                                let uu____7408
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a
                                                                   in
                                                                let uu____7409
                                                                  =
                                                                  let uu____7412
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                  let uu____7413
                                                                    =
                                                                    let uu____7416
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
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
                                                                  uu____7412
                                                                    ::
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
                                                        uu____7449 ::
                                                          uu____7456
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
                                                              let uu____7594
                                                                =
                                                                let uu____7601
                                                                  =
                                                                  let uu____7602
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____7602
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7601
                                                                 in
                                                              let uu____7603
                                                                =
                                                                let uu____7612
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____7619
                                                                  =
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
                                                          uu____7510
                                                          uu____7560
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
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___779_7734
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.is_native_tactic
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.is_native_tactic);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___779_7734.FStar_TypeChecker_Env.erasable_types_tab)
                                                              })
                                                             (fun _7736  ->
                                                                FStar_Pervasives_Native.Some
                                                                  _7736)
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
                                              (let uu____7763 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____7777 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____7777 with
                                                    | (usubst,uvs) ->
                                                        let uu____7800 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____7801 =
                                                          let uu___792_7802 =
                                                            act  in
                                                          let uu____7803 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____7804 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___792_7802.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___792_7802.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___792_7802.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____7803;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____7804
                                                          }  in
                                                        (uu____7800,
                                                          uu____7801))
                                                  in
                                               match uu____7763 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____7808 =
                                                       let uu____7809 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____7809.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____7808 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____7835 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____7835
                                                         then
                                                           let uu____7838 =
                                                             let uu____7841 =
                                                               let uu____7842
                                                                 =
                                                                 let uu____7843
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____7843
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____7842
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____7841
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7838
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____7866 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____7867 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____7867 with
                                                    | (act_typ1,uu____7875,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___809_7878 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.is_native_tactic
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.is_native_tactic);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___809_7878.FStar_TypeChecker_Env.erasable_types_tab)
                                                          }  in
                                                        ((let uu____7881 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____7881
                                                          then
                                                            let uu____7885 =
                                                              FStar_Ident.text_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____7887 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____7889 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____7885
                                                              uu____7887
                                                              uu____7889
                                                          else ());
                                                         (let uu____7894 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____7894
                                                          with
                                                          | (act_defn,uu____7902,g_a)
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
                                                              let uu____7906
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
                                                                    let uu____7942
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____7942
                                                                    with
                                                                    | 
                                                                    (bs2,uu____7954)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____7961
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7961
                                                                     in
                                                                    let uu____7964
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____7964
                                                                    with
                                                                    | 
                                                                    (k1,uu____7978,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____7982
                                                                    ->
                                                                    let uu____7983
                                                                    =
                                                                    let uu____7989
                                                                    =
                                                                    let uu____7991
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____7993
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____7991
                                                                    uu____7993
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____7989)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____7983
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____7906
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
                                                                    let uu____8011
                                                                    =
                                                                    let uu____8012
                                                                    =
                                                                    let uu____8013
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8013
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8012
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8011);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8015
                                                                    =
                                                                    let uu____8016
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8016.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8015
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8041
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8041
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8048
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8048
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8068
                                                                    =
                                                                    let uu____8069
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8069]
                                                                     in
                                                                    let uu____8070
                                                                    =
                                                                    let uu____8081
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8081]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8068;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8070;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8106
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8106))
                                                                    | 
                                                                    uu____8109
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8111
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8133
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8133))
                                                                     in
                                                                    match uu____8111
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
                                                                    let uu___859_8152
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___859_8152.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___859_8152.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___859_8152.FStar_Syntax_Syntax.action_params);
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
                                match uu____6590 with
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
                                      let uu____8195 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8195 ts1
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
                                          uu____8207 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8208 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8209 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___879_8212 = ed2  in
                                      let uu____8213 = cl signature  in
                                      let uu____8214 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___882_8222 = a  in
                                             let uu____8223 =
                                               let uu____8224 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8224
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8249 =
                                               let uu____8250 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8250
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___882_8222.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___882_8222.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___882_8222.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___882_8222.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8223;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8249
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___879_8212.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___879_8212.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___879_8212.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___879_8212.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8213;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8214;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___879_8212.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8276 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8276
                                      then
                                        let uu____8281 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8281
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
        let uu____8307 =
          let uu____8322 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8322 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8307 env ed quals
  
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
        let fail1 uu____8372 =
          let uu____8373 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8379 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8373 uu____8379  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8423)::(wp,uu____8425)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8454 -> fail1 ())
        | uu____8455 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8468 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8468
       then
         let uu____8473 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8473
       else ());
      (let uu____8478 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____8478 with
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
             let uu____8511 =
               ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
                  (let uu____8515 =
                     let uu____8516 =
                       FStar_All.pipe_right src_ed
                         FStar_Syntax_Util.get_layered_effect_base
                        in
                     FStar_All.pipe_right uu____8516 FStar_Util.must  in
                   FStar_Ident.lid_equals uu____8515
                     tgt_ed.FStar_Syntax_Syntax.mname))
                 ||
                 (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered)
                     &&
                     (let uu____8525 =
                        let uu____8526 =
                          FStar_All.pipe_right tgt_ed
                            FStar_Syntax_Util.get_layered_effect_base
                           in
                        FStar_All.pipe_right uu____8526 FStar_Util.must  in
                      FStar_Ident.lid_equals uu____8525
                        src_ed.FStar_Syntax_Syntax.mname))
                    &&
                    (let uu____8534 =
                       FStar_Ident.lid_equals
                         src_ed.FStar_Syntax_Syntax.mname
                         FStar_Parser_Const.effect_PURE_lid
                        in
                     Prims.op_Negation uu____8534))
                in
             if uu____8511
             then
               let uu____8537 =
                 let uu____8543 =
                   let uu____8545 =
                     FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   let uu____8548 =
                     FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   FStar_Util.format2
                     "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                     uu____8545 uu____8548
                    in
                 (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8543)  in
               FStar_Errors.raise_error uu____8537 r
             else ());
            (let uu____8555 =
               if (FStar_List.length us) = Prims.int_zero
               then (env0, us, lift)
               else
                 (let uu____8579 = FStar_Syntax_Subst.open_univ_vars us lift
                     in
                  match uu____8579 with
                  | (us1,lift1) ->
                      let uu____8594 =
                        FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                      (uu____8594, us1, lift1))
                in
             match uu____8555 with
             | (env,us1,lift1) ->
                 let uu____8604 =
                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                 (match uu____8604 with
                  | (lift2,lc,g) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env g;
                       (let lift_ty =
                          FStar_All.pipe_right
                            lc.FStar_TypeChecker_Common.res_typ
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta] env0)
                           in
                        (let uu____8617 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "LayeredEffects")
                            in
                         if uu____8617
                         then
                           let uu____8622 =
                             FStar_Syntax_Print.term_to_string lift2  in
                           let uu____8624 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.print2
                             "Typechecked lift: %s and lift_ty: %s\n"
                             uu____8622 uu____8624
                         else ());
                        (let lift_t_shape_error s =
                           let uu____8638 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.source
                              in
                           let uu____8640 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.target
                              in
                           let uu____8642 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.format4
                             "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                             uu____8638 uu____8640 s uu____8642
                            in
                         let uu____8645 =
                           let uu____8652 =
                             let uu____8657 = FStar_Syntax_Util.type_u ()  in
                             FStar_All.pipe_right uu____8657
                               (fun uu____8674  ->
                                  match uu____8674 with
                                  | (t,u) ->
                                      let uu____8685 =
                                        let uu____8686 =
                                          FStar_Syntax_Syntax.gen_bv "a"
                                            FStar_Pervasives_Native.None t
                                           in
                                        FStar_All.pipe_right uu____8686
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____8685, u))
                              in
                           match uu____8652 with
                           | (a,u_a) ->
                               let rest_bs =
                                 let uu____8705 =
                                   let uu____8706 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____8706.FStar_Syntax_Syntax.n  in
                                 match uu____8705 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____8718) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____8746 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____8746 with
                                      | (a',uu____8756)::bs1 ->
                                          let uu____8776 =
                                            let uu____8777 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one))
                                               in
                                            FStar_All.pipe_right uu____8777
                                              FStar_Pervasives_Native.fst
                                             in
                                          let uu____8875 =
                                            let uu____8888 =
                                              let uu____8891 =
                                                let uu____8892 =
                                                  let uu____8899 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____8899)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____8892
                                                 in
                                              [uu____8891]  in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____8888
                                             in
                                          FStar_All.pipe_right uu____8776
                                            uu____8875)
                                 | uu____8914 ->
                                     let uu____8915 =
                                       let uu____8921 =
                                         lift_t_shape_error
                                           "either not an arrow, or not enough binders"
                                          in
                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                         uu____8921)
                                        in
                                     FStar_Errors.raise_error uu____8915 r
                                  in
                               let uu____8933 =
                                 let uu____8944 =
                                   let uu____8949 =
                                     FStar_TypeChecker_Env.push_binders env
                                       (a :: rest_bs)
                                      in
                                   let uu____8956 =
                                     let uu____8957 =
                                       FStar_All.pipe_right a
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8957
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   FStar_TypeChecker_Util.fresh_effect_repr_en
                                     uu____8949 r
                                     sub1.FStar_Syntax_Syntax.source u_a
                                     uu____8956
                                    in
                                 match uu____8944 with
                                 | (f_sort,g1) ->
                                     let uu____8978 =
                                       let uu____8985 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None
                                           f_sort
                                          in
                                       FStar_All.pipe_right uu____8985
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____8978, g1)
                                  in
                               (match uu____8933 with
                                | (f_b,g_f_b) ->
                                    let bs = a ::
                                      (FStar_List.append rest_bs [f_b])  in
                                    let uu____9052 =
                                      let uu____9057 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9058 =
                                        let uu____9059 =
                                          FStar_All.pipe_right a
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____9059
                                          FStar_Syntax_Syntax.bv_to_name
                                         in
                                      FStar_TypeChecker_Util.fresh_effect_repr_en
                                        uu____9057 r
                                        sub1.FStar_Syntax_Syntax.target u_a
                                        uu____9058
                                       in
                                    (match uu____9052 with
                                     | (repr,g_repr) ->
                                         let uu____9076 =
                                           let uu____9079 =
                                             let uu____9082 =
                                               let uu____9085 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               FStar_All.pipe_right
                                                 uu____9085
                                                 (fun _9088  ->
                                                    FStar_Pervasives_Native.Some
                                                      _9088)
                                                in
                                             FStar_Syntax_Syntax.mk_Total'
                                               repr uu____9082
                                              in
                                           FStar_Syntax_Util.arrow bs
                                             uu____9079
                                            in
                                         let uu____9089 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g_f_b g_repr
                                            in
                                         (uu____9076, uu____9089)))
                            in
                         match uu____8645 with
                         | (k,g_k) ->
                             ((let uu____9099 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____9099
                               then
                                 let uu____9104 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "tc_layered_lift: before unification k: %s\n"
                                   uu____9104
                               else ());
                              (let g1 =
                                 FStar_TypeChecker_Rel.teq env lift_ty k  in
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g_k;
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g1;
                               (let uu____9113 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____9113
                                then
                                  let uu____9118 =
                                    FStar_Syntax_Print.term_to_string k  in
                                  FStar_Util.print1
                                    "After unification k: %s\n" uu____9118
                                else ());
                               (let uu____9123 =
                                  let uu____9136 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 lift2
                                     in
                                  match uu____9136 with
                                  | (inst_us,lift3) ->
                                      (if
                                         (FStar_List.length inst_us) <>
                                           Prims.int_one
                                       then
                                         (let uu____9163 =
                                            let uu____9169 =
                                              let uu____9171 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____9173 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____9175 =
                                                let uu____9177 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____9177
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____9184 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format4
                                                "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                                uu____9171 uu____9173
                                                uu____9175 uu____9184
                                               in
                                            (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                              uu____9169)
                                             in
                                          FStar_Errors.raise_error uu____9163
                                            r)
                                       else ();
                                       (let uu____9190 =
                                          ((FStar_List.length us1) =
                                             Prims.int_zero)
                                            ||
                                            (((FStar_List.length us1) =
                                                (FStar_List.length inst_us))
                                               &&
                                               (FStar_List.forall2
                                                  (fun u1  ->
                                                     fun u2  ->
                                                       let uu____9199 =
                                                         FStar_Syntax_Syntax.order_univ_name
                                                           u1 u2
                                                          in
                                                       uu____9199 =
                                                         Prims.int_zero) us1
                                                  inst_us))
                                           in
                                        if uu____9190
                                        then
                                          let uu____9216 =
                                            let uu____9219 =
                                              FStar_All.pipe_right k
                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                   env)
                                               in
                                            FStar_All.pipe_right uu____9219
                                              (FStar_Syntax_Subst.close_univ_vars
                                                 inst_us)
                                             in
                                          (inst_us, lift3, uu____9216)
                                        else
                                          (let uu____9230 =
                                             let uu____9236 =
                                               let uu____9238 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.source
                                                  in
                                               let uu____9240 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.target
                                                  in
                                               let uu____9242 =
                                                 let uu____9244 =
                                                   FStar_All.pipe_right us1
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9244
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9251 =
                                                 let uu____9253 =
                                                   FStar_All.pipe_right
                                                     inst_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9253
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9260 =
                                                 FStar_Syntax_Print.term_to_string
                                                   lift3
                                                  in
                                               FStar_Util.format5
                                                 "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                 uu____9238 uu____9240
                                                 uu____9242 uu____9251
                                                 uu____9260
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____9236)
                                              in
                                           FStar_Errors.raise_error
                                             uu____9230 r)))
                                   in
                                match uu____9123 with
                                | (us2,lift3,lift_wp) ->
                                    let sub2 =
                                      let uu___990_9292 = sub1  in
                                      {
                                        FStar_Syntax_Syntax.source =
                                          (uu___990_9292.FStar_Syntax_Syntax.source);
                                        FStar_Syntax_Syntax.target =
                                          (uu___990_9292.FStar_Syntax_Syntax.target);
                                        FStar_Syntax_Syntax.lift_wp =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift_wp));
                                        FStar_Syntax_Syntax.lift =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift3))
                                      }  in
                                    ((let uu____9302 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env0)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____9302
                                      then
                                        let uu____9307 =
                                          FStar_Syntax_Print.sub_eff_to_string
                                            sub2
                                           in
                                        FStar_Util.print1
                                          "Final sub_effect: %s\n" uu____9307
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
        let uu____9330 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9330
        then tc_layered_lift env sub1
        else
          (let uu____9337 =
             let uu____9344 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9344
              in
           match uu____9337 with
           | (a,wp_a_src) ->
               let uu____9351 =
                 let uu____9358 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9358
                  in
               (match uu____9351 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9366 =
                        let uu____9369 =
                          let uu____9370 =
                            let uu____9377 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9377)  in
                          FStar_Syntax_Syntax.NT uu____9370  in
                        [uu____9369]  in
                      FStar_Syntax_Subst.subst uu____9366 wp_b_tgt  in
                    let expected_k =
                      let uu____9385 =
                        let uu____9394 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9401 =
                          let uu____9410 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9410]  in
                        uu____9394 :: uu____9401  in
                      let uu____9435 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9385 uu____9435  in
                    let repr_type eff_name a1 wp =
                      (let uu____9457 =
                         let uu____9459 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9459  in
                       if uu____9457
                       then
                         let uu____9462 =
                           let uu____9468 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9468)
                            in
                         let uu____9472 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9462 uu____9472
                       else ());
                      (let uu____9475 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9475 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9508 =
                               let uu____9509 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9509
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9508
                              in
                           let uu____9516 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9517 =
                             let uu____9524 =
                               let uu____9525 =
                                 let uu____9542 =
                                   let uu____9553 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9562 =
                                     let uu____9573 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9573]  in
                                   uu____9553 :: uu____9562  in
                                 (repr, uu____9542)  in
                               FStar_Syntax_Syntax.Tm_app uu____9525  in
                             FStar_Syntax_Syntax.mk uu____9524  in
                           uu____9517 FStar_Pervasives_Native.None uu____9516)
                       in
                    let uu____9618 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9791 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9802 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9802 with
                              | (usubst,uvs1) ->
                                  let uu____9825 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____9826 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____9825, uu____9826)
                            else (env, lift_wp)  in
                          (match uu____9791 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____9876 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____9876))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____9947 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____9962 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____9962 with
                              | (usubst,uvs) ->
                                  let uu____9987 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____9987)
                            else ([], lift)  in
                          (match uu____9947 with
                           | (uvs,lift1) ->
                               ((let uu____10023 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10023
                                 then
                                   let uu____10027 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10027
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10033 =
                                   let uu____10040 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10040 lift1
                                    in
                                 match uu____10033 with
                                 | (lift2,comp,uu____10065) ->
                                     let uu____10066 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10066 with
                                      | (uu____10095,lift_wp,lift_elab) ->
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
                                            let uu____10127 =
                                              let uu____10138 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10138
                                               in
                                            let uu____10155 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10127, uu____10155)
                                          else
                                            (let uu____10184 =
                                               let uu____10195 =
                                                 let uu____10204 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10204)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10195
                                                in
                                             let uu____10219 =
                                               let uu____10228 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10228)  in
                                             (uu____10184, uu____10219))))))
                       in
                    (match uu____9618 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1070_10292 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1070_10292.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1070_10292.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1070_10292.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1070_10292.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1070_10292.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1070_10292.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1070_10292.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1070_10292.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1070_10292.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1070_10292.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1070_10292.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1070_10292.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1070_10292.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1070_10292.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1070_10292.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1070_10292.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1070_10292.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1070_10292.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1070_10292.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1070_10292.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1070_10292.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1070_10292.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1070_10292.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1070_10292.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1070_10292.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1070_10292.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1070_10292.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1070_10292.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1070_10292.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1070_10292.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1070_10292.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1070_10292.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1070_10292.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1070_10292.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1070_10292.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1070_10292.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1070_10292.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1070_10292.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1070_10292.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1070_10292.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1070_10292.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1070_10292.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1070_10292.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1070_10292.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10325 =
                                 let uu____10330 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10330 with
                                 | (usubst,uvs1) ->
                                     let uu____10353 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10354 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10353, uu____10354)
                                  in
                               (match uu____10325 with
                                | (env2,lift2) ->
                                    let uu____10359 =
                                      let uu____10366 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10366
                                       in
                                    (match uu____10359 with
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
                                             let uu____10392 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10393 =
                                               let uu____10400 =
                                                 let uu____10401 =
                                                   let uu____10418 =
                                                     let uu____10429 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10438 =
                                                       let uu____10449 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10449]  in
                                                     uu____10429 ::
                                                       uu____10438
                                                      in
                                                   (lift_wp1, uu____10418)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10401
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10400
                                                in
                                             uu____10393
                                               FStar_Pervasives_Native.None
                                               uu____10392
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10497 =
                                             let uu____10506 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10513 =
                                               let uu____10522 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10529 =
                                                 let uu____10538 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10538]  in
                                               uu____10522 :: uu____10529  in
                                             uu____10506 :: uu____10513  in
                                           let uu____10569 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10497 uu____10569
                                            in
                                         let uu____10572 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10572 with
                                          | (expected_k2,uu____10582,uu____10583)
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
                                                   let uu____10591 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10591))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10599 =
                             let uu____10601 =
                               let uu____10603 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10603
                                 FStar_List.length
                                in
                             uu____10601 <> Prims.int_one  in
                           if uu____10599
                           then
                             let uu____10626 =
                               let uu____10632 =
                                 let uu____10634 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10636 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10638 =
                                   let uu____10640 =
                                     let uu____10642 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10642
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10640
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10634 uu____10636 uu____10638
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10632)
                                in
                             FStar_Errors.raise_error uu____10626 r
                           else ());
                          (let uu____10669 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10672 =
                                  let uu____10674 =
                                    let uu____10677 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10677
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10674
                                    FStar_List.length
                                   in
                                uu____10672 <> Prims.int_one)
                              in
                           if uu____10669
                           then
                             let uu____10716 =
                               let uu____10722 =
                                 let uu____10724 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10726 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10728 =
                                   let uu____10730 =
                                     let uu____10732 =
                                       let uu____10735 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10735
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10732
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10730
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10724 uu____10726 uu____10728
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10722)
                                in
                             FStar_Errors.raise_error uu____10716 r
                           else ());
                          (let uu___1107_10777 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1107_10777.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1107_10777.FStar_Syntax_Syntax.target);
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
    fun uu____10808  ->
      fun r  ->
        match uu____10808 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____10831 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10859 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____10859 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____10890 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____10890 c  in
                     let uu____10899 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____10899, uvs1, tps1, c1))
               in
            (match uu____10831 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____10919 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____10919 with
                  | (tps2,c2) ->
                      let uu____10934 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____10934 with
                       | (tps3,env3,us) ->
                           let uu____10952 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____10952 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____10978)::uu____10979 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____10998 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____11006 =
                                    let uu____11008 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____11008  in
                                  if uu____11006
                                  then
                                    let uu____11011 =
                                      let uu____11017 =
                                        let uu____11019 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11021 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11019 uu____11021
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11017)
                                       in
                                    FStar_Errors.raise_error uu____11011 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11029 =
                                    let uu____11030 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11030
                                     in
                                  match uu____11029 with
                                  | (uvs2,t) ->
                                      let uu____11059 =
                                        let uu____11064 =
                                          let uu____11077 =
                                            let uu____11078 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11078.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11077)  in
                                        match uu____11064 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11093,c5)) -> ([], c5)
                                        | (uu____11135,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11174 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11059 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11206 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11206 with
                                               | (uu____11211,t1) ->
                                                   let uu____11213 =
                                                     let uu____11219 =
                                                       let uu____11221 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11223 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11227 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11221
                                                         uu____11223
                                                         uu____11227
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11219)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11213 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  