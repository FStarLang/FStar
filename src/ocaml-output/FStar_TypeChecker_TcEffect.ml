open Prims
let (dmff_cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  = fun env  -> fun ed  -> FStar_TypeChecker_DMFF.cps_and_elaborate env ed 
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____36 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____36 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun quals  ->
        (let uu____68 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____68
         then
           let uu____73 = FStar_Syntax_Print.eff_decl_to_string false ed  in
           FStar_Util.print1 "Typechecking layered effect: \n\t%s\n" uu____73
         else ());
        if
          ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
            ||
            ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
               Prims.int_zero)
        then
          (let uu____91 =
             FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_UnexpectedEffect,
               (Prims.op_Hat
                  "Binders are not supported for layered effects ("
                  (Prims.op_Hat
                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str ")")))
             uu____91)
        else ();
        (let check_and_gen comb n1 uu____124 =
           match uu____124 with
           | (us,t) ->
               let uu____145 = FStar_Syntax_Subst.open_univ_vars us t  in
               (match uu____145 with
                | (us1,t1) ->
                    let uu____158 =
                      let uu____163 =
                        let uu____170 =
                          FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                          uu____170 t1
                         in
                      match uu____163 with
                      | (t2,lc,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env0 g;
                           (t2, (lc.FStar_TypeChecker_Common.res_typ)))
                       in
                    (match uu____158 with
                     | (t2,ty) ->
                         let uu____187 =
                           FStar_TypeChecker_Util.generalize_universes env0
                             t2
                            in
                         (match uu____187 with
                          | (g_us,t3) ->
                              let ty1 =
                                FStar_Syntax_Subst.close_univ_vars g_us ty
                                 in
                              (if (FStar_List.length g_us) <> n1
                               then
                                 (let error =
                                    let uu____210 =
                                      FStar_Util.string_of_int n1  in
                                    let uu____212 =
                                      let uu____214 =
                                        FStar_All.pipe_right g_us
                                          FStar_List.length
                                         in
                                      FStar_All.pipe_right uu____214
                                        FStar_Util.string_of_int
                                       in
                                    let uu____221 =
                                      FStar_Syntax_Print.tscheme_to_string
                                        (g_us, t3)
                                       in
                                    FStar_Util.format5
                                      "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                      comb uu____210 uu____212 uu____221
                                     in
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                      error) t3.FStar_Syntax_Syntax.pos;
                                  (match us1 with
                                   | [] -> ()
                                   | uu____230 ->
                                       let uu____231 =
                                         ((FStar_List.length us1) =
                                            (FStar_List.length g_us))
                                           &&
                                           (FStar_List.forall2
                                              (fun u1  ->
                                                 fun u2  ->
                                                   let uu____238 =
                                                     FStar_Syntax_Syntax.order_univ_name
                                                       u1 u2
                                                      in
                                                   uu____238 = Prims.int_zero)
                                              us1 g_us)
                                          in
                                       if uu____231
                                       then ()
                                       else
                                         (let uu____245 =
                                            let uu____251 =
                                              let uu____253 =
                                                FStar_Syntax_Print.univ_names_to_string
                                                  us1
                                                 in
                                              let uu____255 =
                                                FStar_Syntax_Print.univ_names_to_string
                                                  g_us
                                                 in
                                              FStar_Util.format4
                                                "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                comb uu____253 uu____255
                                               in
                                            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                              uu____251)
                                             in
                                          FStar_Errors.raise_error uu____245
                                            t3.FStar_Syntax_Syntax.pos)))
                               else ();
                               (g_us, t3, ty1)))))
            in
         let log_combinator s uu____284 =
           match uu____284 with
           | (us,t,ty) ->
               let uu____313 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____313
               then
                 let uu____318 = FStar_Syntax_Print.tscheme_to_string (us, t)
                    in
                 let uu____324 =
                   FStar_Syntax_Print.tscheme_to_string (us, ty)  in
                 FStar_Util.print4 "Typechecked %s:%s = %s:%s\n"
                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str s uu____318
                   uu____324
               else ()
            in
         let fresh_a_and_u_a a =
           let uu____349 = FStar_Syntax_Util.type_u ()  in
           FStar_All.pipe_right uu____349
             (fun uu____366  ->
                match uu____366 with
                | (t,u) ->
                    let uu____377 =
                      let uu____378 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t
                         in
                      FStar_All.pipe_right uu____378
                        FStar_Syntax_Syntax.mk_binder
                       in
                    (uu____377, u))
            in
         let fresh_x_a x a =
           let uu____392 =
             let uu____393 =
               let uu____394 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
               FStar_All.pipe_right uu____394 FStar_Syntax_Syntax.bv_to_name
                in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____393
              in
           FStar_All.pipe_right uu____392 FStar_Syntax_Syntax.mk_binder  in
         let signature =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
              in
           let uu____421 =
             check_and_gen "signature" Prims.int_one
               ed.FStar_Syntax_Syntax.signature
              in
           match uu____421 with
           | (sig_us,sig_t,sig_ty) ->
               let uu____445 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                  in
               (match uu____445 with
                | (us,t) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____465 = fresh_a_and_u_a "a"  in
                    (match uu____465 with
                     | (a,u) ->
                         let rest_bs =
                           let uu____486 =
                             let uu____487 =
                               FStar_All.pipe_right a
                                 FStar_Pervasives_Native.fst
                                in
                             FStar_All.pipe_right uu____487
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           FStar_TypeChecker_Util.layered_effect_indices_as_binders
                             env r ed.FStar_Syntax_Syntax.mname
                             (sig_us, sig_t) u uu____486
                            in
                         let bs = a :: rest_bs  in
                         let k =
                           let uu____518 =
                             FStar_Syntax_Syntax.mk_Total
                               FStar_Syntax_Syntax.teff
                              in
                           FStar_Syntax_Util.arrow bs uu____518  in
                         let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                         (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                          (let uu____523 =
                             let uu____526 =
                               FStar_All.pipe_right k
                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                    env)
                                in
                             FStar_Syntax_Subst.close_univ_vars us uu____526
                              in
                           (sig_us, uu____523, sig_ty)))))
            in
         log_combinator "signature" signature;
         (let uu____535 =
            let r =
              (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.pos
               in
            let uu____557 =
              check_and_gen "repr" Prims.int_one ed.FStar_Syntax_Syntax.repr
               in
            match uu____557 with
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
                  let uu____588 =
                    let uu____589 = FStar_Syntax_Subst.compress repr_t1  in
                    uu____589.FStar_Syntax_Syntax.n  in
                  match uu____588 with
                  | FStar_Syntax_Syntax.Tm_abs (uu____592,t,uu____594) ->
                      let uu____619 =
                        let uu____620 = FStar_Syntax_Subst.compress t  in
                        uu____620.FStar_Syntax_Syntax.n  in
                      (match uu____619 with
                       | FStar_Syntax_Syntax.Tm_arrow (uu____623,c) ->
                           let uu____645 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____645
                             (FStar_TypeChecker_Env.norm_eff_name env0)
                       | uu____648 ->
                           let uu____649 =
                             let uu____655 =
                               let uu____657 =
                                 FStar_All.pipe_right
                                   ed.FStar_Syntax_Syntax.mname
                                   FStar_Ident.string_of_lid
                                  in
                               let uu____660 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.format2
                                 "repr body for %s is not an arrow (%s)"
                                 uu____657 uu____660
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu____655)
                              in
                           FStar_Errors.raise_error uu____649 r)
                  | uu____664 ->
                      let uu____665 =
                        let uu____671 =
                          let uu____673 =
                            FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                              FStar_Ident.string_of_lid
                             in
                          let uu____676 =
                            FStar_Syntax_Print.term_to_string repr_t1  in
                          FStar_Util.format2
                            "repr for %s is not an abstraction (%s)"
                            uu____673 uu____676
                           in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____671)  in
                      FStar_Errors.raise_error uu____665 r
                   in
                ((let uu____681 =
                    (FStar_All.pipe_right quals
                       (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                      &&
                      (let uu____687 =
                         FStar_TypeChecker_Env.is_total_effect env0
                           underlying_effect_lid
                          in
                       Prims.op_Negation uu____687)
                     in
                  if uu____681
                  then
                    let uu____690 =
                      let uu____696 =
                        let uu____698 =
                          FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                            FStar_Ident.string_of_lid
                           in
                        let uu____701 =
                          FStar_All.pipe_right underlying_effect_lid
                            FStar_Ident.string_of_lid
                           in
                        FStar_Util.format2
                          "Effect %s is marked total but its underlying effect %s is not total"
                          uu____698 uu____701
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____696)
                       in
                    FStar_Errors.raise_error uu____690 r
                  else ());
                 (let uu____708 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
                  match uu____708 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____732 = fresh_a_and_u_a "a"  in
                      (match uu____732 with
                       | (a,u) ->
                           let rest_bs =
                             let signature_ts =
                               let uu____758 = signature  in
                               match uu____758 with
                               | (us1,t,uu____773) -> (us1, t)  in
                             let uu____790 =
                               let uu____791 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____791
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               signature_ts u uu____790
                              in
                           let bs = a :: rest_bs  in
                           let k =
                             let uu____818 =
                               let uu____821 = FStar_Syntax_Util.type_u ()
                                  in
                               FStar_All.pipe_right uu____821
                                 (fun uu____834  ->
                                    match uu____834 with
                                    | (t,u1) ->
                                        let uu____841 =
                                          let uu____844 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____844
                                           in
                                        FStar_Syntax_Syntax.mk_Total' t
                                          uu____841)
                                in
                             FStar_Syntax_Util.arrow bs uu____818  in
                           let g = FStar_TypeChecker_Rel.teq env ty k  in
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (let uu____847 =
                               let uu____860 =
                                 let uu____863 =
                                   FStar_All.pipe_right k
                                     (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                        env)
                                    in
                                 FStar_Syntax_Subst.close_univ_vars us
                                   uu____863
                                  in
                               (repr_us, repr_t, uu____860)  in
                             (uu____847, underlying_effect_lid))))))
             in
          match uu____535 with
          | (repr,underlying_effect_lid) ->
              (log_combinator "repr" repr;
               (let fresh_repr r env u a_tm =
                  let signature_ts =
                    let uu____936 = signature  in
                    match uu____936 with | (us,t,uu____951) -> (us, t)  in
                  let repr_ts =
                    let uu____969 = repr  in
                    match uu____969 with | (us,t,uu____984) -> (us, t)  in
                  FStar_TypeChecker_Util.fresh_effect_repr env r
                    ed.FStar_Syntax_Syntax.mname signature_ts repr_ts u a_tm
                   in
                let not_an_arrow_error comb n1 t r =
                  let uu____1034 =
                    let uu____1040 =
                      let uu____1042 = FStar_Util.string_of_int n1  in
                      let uu____1044 = FStar_Syntax_Print.tag_of_term t  in
                      let uu____1046 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.format5
                        "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                        (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str comb
                        uu____1042 uu____1044 uu____1046
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____1040)  in
                  FStar_Errors.raise_error uu____1034 r  in
                let return_repr =
                  let r =
                    (FStar_Pervasives_Native.snd
                       ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                     in
                  let uu____1076 =
                    check_and_gen "return_repr" Prims.int_one
                      ed.FStar_Syntax_Syntax.return_repr
                     in
                  match uu____1076 with
                  | (ret_us,ret_t,ret_ty) ->
                      let uu____1100 =
                        FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                      (match uu____1100 with
                       | (us,ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us  in
                           let uu____1120 = fresh_a_and_u_a "a"  in
                           (match uu____1120 with
                            | (a,u_a) ->
                                let rest_bs =
                                  let uu____1149 =
                                    let uu____1150 =
                                      FStar_Syntax_Subst.compress ty  in
                                    uu____1150.FStar_Syntax_Syntax.n  in
                                  match uu____1149 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____1162) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (2))
                                      ->
                                      let uu____1190 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____1190 with
                                       | (a',uu____1200)::bs1 ->
                                           let uu____1220 =
                                             let uu____1221 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - Prims.int_one))
                                                in
                                             FStar_All.pipe_right uu____1221
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____1319 =
                                             let uu____1332 =
                                               let uu____1335 =
                                                 let uu____1336 =
                                                   let uu____1343 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       (FStar_Pervasives_Native.fst
                                                          a)
                                                      in
                                                   (a', uu____1343)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____1336
                                                  in
                                               [uu____1335]  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____1332
                                              in
                                           FStar_All.pipe_right uu____1220
                                             uu____1319)
                                  | uu____1358 ->
                                      not_an_arrow_error "return"
                                        (Prims.of_int (2)) ty r
                                   in
                                let bs =
                                  let uu____1370 =
                                    let uu____1379 =
                                      let uu____1388 = fresh_x_a "x" a  in
                                      [uu____1388]  in
                                    FStar_List.append rest_bs uu____1379  in
                                  a :: uu____1370  in
                                let uu____1420 =
                                  let uu____1425 =
                                    FStar_TypeChecker_Env.push_binders env bs
                                     in
                                  let uu____1426 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst a)
                                      FStar_Syntax_Syntax.bv_to_name
                                     in
                                  fresh_repr r uu____1425 u_a uu____1426  in
                                (match uu____1420 with
                                 | (repr1,g) ->
                                     let k =
                                       let uu____1446 =
                                         FStar_Syntax_Syntax.mk_Total' repr1
                                           (FStar_Pervasives_Native.Some u_a)
                                          in
                                       FStar_Syntax_Util.arrow bs uu____1446
                                        in
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env ty k  in
                                     ((let uu____1451 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           g_eq
                                          in
                                       FStar_TypeChecker_Rel.force_trivial_guard
                                         env uu____1451);
                                      (let uu____1452 =
                                         let uu____1455 =
                                           FStar_All.pipe_right k
                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                env)
                                            in
                                         FStar_Syntax_Subst.close_univ_vars
                                           us uu____1455
                                          in
                                       (ret_us, ret_t, uu____1452))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let r =
                     (FStar_Pervasives_Native.snd
                        ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                      in
                   let uu____1482 =
                     check_and_gen "bind_repr" (Prims.of_int (2))
                       ed.FStar_Syntax_Syntax.bind_repr
                      in
                   match uu____1482 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1506 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1506 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            let uu____1526 = fresh_a_and_u_a "a"  in
                            (match uu____1526 with
                             | (a,u_a) ->
                                 let uu____1546 = fresh_a_and_u_a "b"  in
                                 (match uu____1546 with
                                  | (b,u_b) ->
                                      let rest_bs =
                                        let uu____1575 =
                                          let uu____1576 =
                                            FStar_Syntax_Subst.compress ty
                                             in
                                          uu____1576.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1575 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs,uu____1588) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (4))
                                            ->
                                            let uu____1616 =
                                              FStar_Syntax_Subst.open_binders
                                                bs
                                               in
                                            (match uu____1616 with
                                             | (a',uu____1626)::(b',uu____1628)::bs1
                                                 ->
                                                 let uu____1658 =
                                                   let uu____1659 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             -
                                                             (Prims.of_int (2))))
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____1659
                                                     FStar_Pervasives_Native.fst
                                                    in
                                                 let uu____1725 =
                                                   let uu____1738 =
                                                     let uu____1741 =
                                                       let uu____1742 =
                                                         let uu____1749 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                a)
                                                            in
                                                         (a', uu____1749)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____1742
                                                        in
                                                     let uu____1756 =
                                                       let uu____1759 =
                                                         let uu____1760 =
                                                           let uu____1767 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               (FStar_Pervasives_Native.fst
                                                                  b)
                                                              in
                                                           (b', uu____1767)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____1760
                                                          in
                                                       [uu____1759]  in
                                                     uu____1741 :: uu____1756
                                                      in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____1738
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____1658 uu____1725)
                                        | uu____1782 ->
                                            not_an_arrow_error "bind"
                                              (Prims.of_int (4)) ty r
                                         in
                                      let bs = a :: b :: rest_bs  in
                                      let uu____1806 =
                                        let uu____1817 =
                                          let uu____1822 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____1823 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____1822 u_a
                                            uu____1823
                                           in
                                        match uu____1817 with
                                        | (repr1,g) ->
                                            let uu____1838 =
                                              let uu____1845 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1
                                                 in
                                              FStar_All.pipe_right uu____1845
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            (uu____1838, g)
                                         in
                                      (match uu____1806 with
                                       | (f,guard_f) ->
                                           let uu____1885 =
                                             let x_a = fresh_x_a "x" a  in
                                             let uu____1898 =
                                               let uu____1903 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env
                                                   (FStar_List.append bs
                                                      [x_a])
                                                  in
                                               let uu____1922 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.fst
                                                      b)
                                                   FStar_Syntax_Syntax.bv_to_name
                                                  in
                                               fresh_repr r uu____1903 u_b
                                                 uu____1922
                                                in
                                             match uu____1898 with
                                             | (repr1,g) ->
                                                 let uu____1937 =
                                                   let uu____1944 =
                                                     let uu____1945 =
                                                       let uu____1946 =
                                                         let uu____1949 =
                                                           let uu____1952 =
                                                             FStar_TypeChecker_Env.new_u_univ
                                                               ()
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1952
                                                            in
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1 uu____1949
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         [x_a] uu____1946
                                                        in
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "g"
                                                       FStar_Pervasives_Native.None
                                                       uu____1945
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____1944
                                                     FStar_Syntax_Syntax.mk_binder
                                                    in
                                                 (uu____1937, g)
                                              in
                                           (match uu____1885 with
                                            | (g,guard_g) ->
                                                let uu____2004 =
                                                  let uu____2009 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____2010 =
                                                    FStar_All.pipe_right
                                                      (FStar_Pervasives_Native.fst
                                                         b)
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____2009 u_b
                                                    uu____2010
                                                   in
                                                (match uu____2004 with
                                                 | (repr1,guard_repr) ->
                                                     let k =
                                                       let uu____2030 =
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1
                                                           (FStar_Pervasives_Native.Some
                                                              u_b)
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         (FStar_List.append
                                                            bs [f; g])
                                                         uu____2030
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
                                                      (let uu____2059 =
                                                         let uu____2062 =
                                                           FStar_All.pipe_right
                                                             k
                                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                env)
                                                            in
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           bind_us uu____2062
                                                          in
                                                       (bind_us, bind_t,
                                                         uu____2059)))))))))
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
                    let uu____2104 =
                      check_and_gen "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2104 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2129 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2129
                          then
                            let uu____2134 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2140 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2134 uu____2140
                          else ());
                         (let uu____2149 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2149 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              let uu____2169 = fresh_a_and_u_a "a"  in
                              (match uu____2169 with
                               | (a,u) ->
                                   let rest_bs =
                                     let uu____2198 =
                                       let uu____2199 =
                                         FStar_Syntax_Subst.compress ty  in
                                       uu____2199.FStar_Syntax_Syntax.n  in
                                     match uu____2198 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (bs,uu____2211) when
                                         (FStar_List.length bs) >=
                                           (Prims.of_int (2))
                                         ->
                                         let uu____2239 =
                                           FStar_Syntax_Subst.open_binders bs
                                            in
                                         (match uu____2239 with
                                          | (a',uu____2249)::bs1 ->
                                              let uu____2269 =
                                                let uu____2270 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.splitAt
                                                       ((FStar_List.length
                                                           bs1)
                                                          - Prims.int_one))
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2270
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              let uu____2368 =
                                                let uu____2381 =
                                                  let uu____2384 =
                                                    let uu____2385 =
                                                      let uu____2392 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____2392)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____2385
                                                     in
                                                  [uu____2384]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____2381
                                                 in
                                              FStar_All.pipe_right uu____2269
                                                uu____2368)
                                     | uu____2407 ->
                                         not_an_arrow_error "stronger"
                                           (Prims.of_int (2)) ty r
                                      in
                                   let bs = a :: rest_bs  in
                                   let uu____2425 =
                                     let uu____2436 =
                                       let uu____2441 =
                                         FStar_TypeChecker_Env.push_binders
                                           env bs
                                          in
                                       let uu____2442 =
                                         FStar_All.pipe_right
                                           (FStar_Pervasives_Native.fst a)
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       fresh_repr r uu____2441 u uu____2442
                                        in
                                     match uu____2436 with
                                     | (repr1,g) ->
                                         let uu____2457 =
                                           let uu____2464 =
                                             FStar_Syntax_Syntax.gen_bv "f"
                                               FStar_Pervasives_Native.None
                                               repr1
                                              in
                                           FStar_All.pipe_right uu____2464
                                             FStar_Syntax_Syntax.mk_binder
                                            in
                                         (uu____2457, g)
                                      in
                                   (match uu____2425 with
                                    | (f,guard_f) ->
                                        let uu____2504 =
                                          let uu____2509 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____2510 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____2509 u
                                            uu____2510
                                           in
                                        (match uu____2504 with
                                         | (ret_t,guard_ret_t) ->
                                             let pure_wp_t =
                                               let pure_wp_ts =
                                                 let uu____2529 =
                                                   FStar_TypeChecker_Env.lookup_definition
                                                     [FStar_TypeChecker_Env.NoDelta]
                                                     env
                                                     FStar_Parser_Const.pure_wp_lid
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2529 FStar_Util.must
                                                  in
                                               let uu____2546 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   pure_wp_ts
                                                  in
                                               match uu____2546 with
                                               | (uu____2551,pure_wp_t) ->
                                                   let uu____2553 =
                                                     let uu____2558 =
                                                       let uu____2559 =
                                                         FStar_All.pipe_right
                                                           ret_t
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____2559]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       pure_wp_t uu____2558
                                                      in
                                                   uu____2553
                                                     FStar_Pervasives_Native.None
                                                     r
                                                in
                                             let uu____2592 =
                                               let reason =
                                                 FStar_Util.format1
                                                   "implicit for pure_wp in checking stronger for %s"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                  in
                                               let uu____2608 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs
                                                  in
                                               FStar_TypeChecker_Util.new_implicit_var
                                                 reason r uu____2608
                                                 pure_wp_t
                                                in
                                             (match uu____2592 with
                                              | (pure_wp_uvar,uu____2622,guard_wp)
                                                  ->
                                                  let c =
                                                    let uu____2637 =
                                                      let uu____2638 =
                                                        let uu____2639 =
                                                          FStar_TypeChecker_Env.new_u_univ
                                                            ()
                                                           in
                                                        [uu____2639]  in
                                                      let uu____2640 =
                                                        let uu____2651 =
                                                          FStar_All.pipe_right
                                                            pure_wp_uvar
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____2651]  in
                                                      {
                                                        FStar_Syntax_Syntax.comp_univs
                                                          = uu____2638;
                                                        FStar_Syntax_Syntax.effect_name
                                                          =
                                                          FStar_Parser_Const.effect_PURE_lid;
                                                        FStar_Syntax_Syntax.result_typ
                                                          = ret_t;
                                                        FStar_Syntax_Syntax.effect_args
                                                          = uu____2640;
                                                        FStar_Syntax_Syntax.flags
                                                          = []
                                                      }  in
                                                    FStar_Syntax_Syntax.mk_Comp
                                                      uu____2637
                                                     in
                                                  let k =
                                                    FStar_Syntax_Util.arrow
                                                      (FStar_List.append bs
                                                         [f]) c
                                                     in
                                                  ((let uu____2706 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "LayeredEffects")
                                                       in
                                                    if uu____2706
                                                    then
                                                      let uu____2711 =
                                                        FStar_Syntax_Print.term_to_string
                                                          k
                                                         in
                                                      FStar_Util.print1
                                                        "Expected type before unification: %s\n"
                                                        uu____2711
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
                                                     let uu____2719 =
                                                       let uu____2722 =
                                                         FStar_All.pipe_right
                                                           k1
                                                           (FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Env.Beta;
                                                              FStar_TypeChecker_Env.Eager_unfolding]
                                                              env)
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____2722
                                                         (FStar_Syntax_Subst.close_univ_vars
                                                            stronger_us)
                                                        in
                                                     (stronger_us,
                                                       stronger_t,
                                                       uu____2719))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2747 =
                         FStar_All.pipe_right
                           ed.FStar_Syntax_Syntax.match_wps FStar_Util.right
                          in
                       uu____2747.FStar_Syntax_Syntax.sif_then_else  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2757 =
                       check_and_gen "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2757 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2781 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2781 with
                          | (us,t) ->
                              let uu____2800 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2800 with
                               | (uu____2817,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   let uu____2820 = fresh_a_and_u_a "a"  in
                                   (match uu____2820 with
                                    | (a,u_a) ->
                                        let rest_bs =
                                          let uu____2849 =
                                            let uu____2850 =
                                              FStar_Syntax_Subst.compress ty
                                               in
                                            uu____2850.FStar_Syntax_Syntax.n
                                             in
                                          match uu____2849 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,uu____2862) when
                                              (FStar_List.length bs) >=
                                                (Prims.of_int (4))
                                              ->
                                              let uu____2890 =
                                                FStar_Syntax_Subst.open_binders
                                                  bs
                                                 in
                                              (match uu____2890 with
                                               | (a',uu____2900)::bs1 ->
                                                   let uu____2920 =
                                                     let uu____2921 =
                                                       FStar_All.pipe_right
                                                         bs1
                                                         (FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs1)
                                                               -
                                                               (Prims.of_int (3))))
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____2921
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____3019 =
                                                     let uu____3032 =
                                                       let uu____3035 =
                                                         let uu____3036 =
                                                           let uu____3043 =
                                                             let uu____3046 =
                                                               FStar_All.pipe_right
                                                                 a
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____3046
                                                               FStar_Syntax_Syntax.bv_to_name
                                                              in
                                                           (a', uu____3043)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____3036
                                                          in
                                                       [uu____3035]  in
                                                     FStar_Syntax_Subst.subst_binders
                                                       uu____3032
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____2920 uu____3019)
                                          | uu____3067 ->
                                              not_an_arrow_error
                                                "if_then_else"
                                                (Prims.of_int (4)) ty r
                                           in
                                        let bs = a :: rest_bs  in
                                        let uu____3085 =
                                          let uu____3096 =
                                            let uu____3101 =
                                              FStar_TypeChecker_Env.push_binders
                                                env bs
                                               in
                                            let uu____3102 =
                                              let uu____3103 =
                                                FStar_All.pipe_right a
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right uu____3103
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            fresh_repr r uu____3101 u_a
                                              uu____3102
                                             in
                                          match uu____3096 with
                                          | (repr1,g) ->
                                              let uu____3124 =
                                                let uu____3131 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "f"
                                                    FStar_Pervasives_Native.None
                                                    repr1
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3131
                                                  FStar_Syntax_Syntax.mk_binder
                                                 in
                                              (uu____3124, g)
                                           in
                                        (match uu____3085 with
                                         | (f_bs,guard_f) ->
                                             let uu____3171 =
                                               let uu____3182 =
                                                 let uu____3187 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env bs
                                                    in
                                                 let uu____3188 =
                                                   let uu____3189 =
                                                     FStar_All.pipe_right a
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3189
                                                     FStar_Syntax_Syntax.bv_to_name
                                                    in
                                                 fresh_repr r uu____3187 u_a
                                                   uu____3188
                                                  in
                                               match uu____3182 with
                                               | (repr1,g) ->
                                                   let uu____3210 =
                                                     let uu____3217 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "g"
                                                         FStar_Pervasives_Native.None
                                                         repr1
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3217
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   (uu____3210, g)
                                                in
                                             (match uu____3171 with
                                              | (g_bs,guard_g) ->
                                                  let p_b =
                                                    let uu____3264 =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "p"
                                                        FStar_Pervasives_Native.None
                                                        FStar_Syntax_Util.ktype0
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3264
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  let uu____3272 =
                                                    let uu____3277 =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env
                                                        (FStar_List.append bs
                                                           [p_b])
                                                       in
                                                    let uu____3296 =
                                                      let uu____3297 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3297
                                                        FStar_Syntax_Syntax.bv_to_name
                                                       in
                                                    fresh_repr r uu____3277
                                                      u_a uu____3296
                                                     in
                                                  (match uu____3272 with
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
                                                        (let uu____3357 =
                                                           let uu____3360 =
                                                             FStar_All.pipe_right
                                                               k
                                                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                  env)
                                                              in
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             if_then_else_us
                                                             uu____3360
                                                            in
                                                         (if_then_else_us,
                                                           uu____3357,
                                                           if_then_else_ty)))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3371 =
                        let uu____3374 =
                          let uu____3383 =
                            FStar_All.pipe_right
                              ed.FStar_Syntax_Syntax.match_wps
                              FStar_Util.right
                             in
                          uu____3383.FStar_Syntax_Syntax.sif_then_else  in
                        FStar_All.pipe_right uu____3374
                          FStar_Pervasives_Native.snd
                         in
                      uu____3371.FStar_Syntax_Syntax.pos  in
                    let uu____3402 = if_then_else1  in
                    match uu____3402 with
                    | (ite_us,ite_t,uu____3417) ->
                        let uu____3430 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3430 with
                         | (us,ite_t1) ->
                             let uu____3437 =
                               let uu____3448 =
                                 let uu____3449 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3449.FStar_Syntax_Syntax.n  in
                               match uu____3448 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3463,uu____3464) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3490 =
                                     let uu____3503 =
                                       let uu____3508 =
                                         let uu____3511 =
                                           let uu____3520 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3520
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3511
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3508
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3503
                                       (fun l  ->
                                          let uu____3676 = l  in
                                          match uu____3676 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3490 with
                                    | (f,g,p) ->
                                        let uu____3741 =
                                          let uu____3742 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3742 bs1
                                           in
                                        let uu____3743 =
                                          let uu____3744 =
                                            let uu____3749 =
                                              let uu____3750 =
                                                let uu____3753 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3753
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____3750
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____3749
                                             in
                                          uu____3744
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____3741, uu____3743, f, g, p))
                               | uu____3780 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3437 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____3797 =
                                    let uu____3806 = stronger_repr  in
                                    match uu____3806 with
                                    | (uu____3827,subcomp_t,subcomp_ty) ->
                                        let uu____3842 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3842 with
                                         | (uu____3855,subcomp_t1) ->
                                             let bs_except_last =
                                               let uu____3866 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____3866 with
                                               | (uu____3879,subcomp_ty1) ->
                                                   let uu____3881 =
                                                     let uu____3882 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____3882.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____3881 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____3894) ->
                                                        let uu____3915 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3915
                                                          FStar_Pervasives_Native.fst
                                                    | uu____4021 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             let aux t =
                                               let uu____4039 =
                                                 let uu____4044 =
                                                   let uu____4045 =
                                                     let uu____4048 =
                                                       FStar_All.pipe_right
                                                         bs_except_last
                                                         (FStar_List.map
                                                            (fun uu____4068 
                                                               ->
                                                               FStar_Syntax_Syntax.tun))
                                                        in
                                                     FStar_List.append
                                                       uu____4048 [t]
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____4045
                                                     (FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg)
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   subcomp_t1 uu____4044
                                                  in
                                               uu____4039
                                                 FStar_Pervasives_Native.None
                                                 r
                                                in
                                             let uu____4077 = aux f_t  in
                                             let uu____4080 = aux g_t  in
                                             (uu____4077, uu____4080))
                                     in
                                  (match uu____3797 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4097 =
                                         let aux t =
                                           let uu____4114 =
                                             let uu____4121 =
                                               let uu____4122 =
                                                 let uu____4149 =
                                                   let uu____4166 =
                                                     let uu____4175 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4175
                                                      in
                                                   (uu____4166,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4149,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4122
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4121
                                              in
                                           uu____4114
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4216 = aux subcomp_f  in
                                         let uu____4217 = aux subcomp_g  in
                                         (uu____4216, uu____4217)  in
                                       (match uu____4097 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4221 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4221
                                              then
                                                let uu____4226 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4228 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4226 uu____4228
                                              else ());
                                             (let uu____4233 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4233 with
                                              | (uu____4240,uu____4241,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4244 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4244 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4246 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4246 with
                                                    | (uu____4253,uu____4254,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4260 =
                                                              let uu____4265
                                                                =
                                                                let uu____4266
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4266
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4267
                                                                =
                                                                let uu____4268
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4268]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4265
                                                                uu____4267
                                                               in
                                                            uu____4260
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4301 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4301 g_g
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
                        (let uu____4325 =
                           let uu____4331 =
                             let uu____4333 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4333
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4331)
                            in
                         FStar_Errors.raise_error uu____4325 r)
                      else ();
                      (let uu____4340 =
                         let uu____4345 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4345 with
                         | (usubst,us) ->
                             let uu____4368 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4369 =
                               let uu___418_4370 = act  in
                               let uu____4371 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4372 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___418_4370.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___418_4370.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___418_4370.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4371;
                                 FStar_Syntax_Syntax.action_typ = uu____4372
                               }  in
                             (uu____4368, uu____4369)
                          in
                       match uu____4340 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4376 =
                               let uu____4377 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4377.FStar_Syntax_Syntax.n  in
                             match uu____4376 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4403 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4403
                                 then
                                   let repr_ts =
                                     let uu____4407 = repr  in
                                     match uu____4407 with
                                     | (us,t,uu____4422) -> (us, t)  in
                                   let repr1 =
                                     let uu____4440 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4440
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4452 =
                                       let uu____4457 =
                                         let uu____4458 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4458 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4457
                                        in
                                     uu____4452 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4476 =
                                       let uu____4479 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4479
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4476
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4482 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4483 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4483 with
                            | (act_typ1,uu____4491,g_t) ->
                                let uu____4493 =
                                  let uu____4500 =
                                    let uu___443_4501 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___443_4501.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___443_4501.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___443_4501.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___443_4501.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___443_4501.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___443_4501.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___443_4501.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___443_4501.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___443_4501.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___443_4501.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___443_4501.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___443_4501.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___443_4501.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___443_4501.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___443_4501.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___443_4501.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___443_4501.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___443_4501.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___443_4501.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___443_4501.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___443_4501.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___443_4501.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___443_4501.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___443_4501.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___443_4501.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___443_4501.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___443_4501.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___443_4501.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___443_4501.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___443_4501.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___443_4501.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___443_4501.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___443_4501.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___443_4501.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___443_4501.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___443_4501.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___443_4501.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___443_4501.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___443_4501.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___443_4501.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___443_4501.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___443_4501.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___443_4501.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___443_4501.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4500
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4493 with
                                 | (act_defn,uu____4504,g_d) ->
                                     ((let uu____4507 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4507
                                       then
                                         let uu____4512 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4514 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4512 uu____4514
                                       else ());
                                      (let uu____4519 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4527 =
                                           let uu____4528 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4528.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4527 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4538) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4561 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4561 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4577 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4577 with
                                                   | (a_tm,uu____4597,g_tm)
                                                       ->
                                                       let uu____4611 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4611 with
                                                        | (repr1,g) ->
                                                            let uu____4624 =
                                                              let uu____4627
                                                                =
                                                                let uu____4630
                                                                  =
                                                                  let uu____4633
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4633
                                                                    (
                                                                    fun _4636
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4636)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4630
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4627
                                                               in
                                                            let uu____4637 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4624,
                                                              uu____4637))))
                                         | uu____4640 ->
                                             let uu____4641 =
                                               let uu____4647 =
                                                 let uu____4649 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____4649
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4647)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4641 r
                                          in
                                       match uu____4519 with
                                       | (k,g_k) ->
                                           ((let uu____4666 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4666
                                             then
                                               let uu____4671 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4671
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4679 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4679
                                              then
                                                let uu____4684 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4684
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4697 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____4697
                                                   in
                                                let repr_args t =
                                                  let uu____4718 =
                                                    let uu____4719 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4719.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4718 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4771 =
                                                        let uu____4772 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4772.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4771 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4781,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4791 ->
                                                           let uu____4792 =
                                                             let uu____4798 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4798)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4792 r)
                                                  | uu____4807 ->
                                                      let uu____4808 =
                                                        let uu____4814 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4814)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4808 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4824 =
                                                  let uu____4825 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4825.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4824 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4850 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4850 with
                                                     | (bs1,c1) ->
                                                         let uu____4857 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____4857
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
                                                              let uu____4868
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4868))
                                                | uu____4871 ->
                                                    let uu____4872 =
                                                      let uu____4878 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____4878)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____4872 r
                                                 in
                                              (let uu____4882 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____4882
                                               then
                                                 let uu____4887 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____4887
                                               else ());
                                              (let act2 =
                                                 let uu____4893 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____4893 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___516_4907 =
                                                         act1  in
                                                       let uu____4908 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___516_4907.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___516_4907.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___516_4907.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____4908
                                                       }
                                                     else
                                                       (let uu____4911 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____4918
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____4918
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____4911
                                                        then
                                                          let uu___521_4923 =
                                                            act1  in
                                                          let uu____4924 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___521_4923.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___521_4923.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___521_4923.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___521_4923.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____4924
                                                          }
                                                        else
                                                          (let uu____4927 =
                                                             let uu____4933 =
                                                               let uu____4935
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____4937
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____4935
                                                                 uu____4937
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____4933)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4927 r))
                                                  in
                                               act2)))))))))
                       in
                    let fst1 uu____4960 =
                      match uu____4960 with | (a,uu____4976,uu____4977) -> a
                       in
                    let snd1 uu____5009 =
                      match uu____5009 with | (uu____5024,b,uu____5026) -> b
                       in
                    let thd uu____5058 =
                      match uu____5058 with | (uu____5073,uu____5074,c) -> c
                       in
                    let uu___539_5088 = ed  in
                    let uu____5089 =
                      FStar_All.pipe_right
                        ((fst1 stronger_repr), (snd1 stronger_repr))
                        (fun _5098  -> FStar_Pervasives_Native.Some _5098)
                       in
                    let uu____5099 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.is_layered =
                        (true,
                          (FStar_Pervasives_Native.Some underlying_effect_lid));
                      FStar_Syntax_Syntax.cattributes =
                        (uu___539_5088.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.mname =
                        (uu___539_5088.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.univs =
                        (uu___539_5088.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___539_5088.FStar_Syntax_Syntax.binders);
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
                        (uu___539_5088.FStar_Syntax_Syntax.trivial);
                      FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
                      FStar_Syntax_Syntax.return_repr =
                        ((fst1 return_repr), (snd1 return_repr));
                      FStar_Syntax_Syntax.bind_repr =
                        ((fst1 bind_repr), (snd1 bind_repr));
                      FStar_Syntax_Syntax.stronger_repr = uu____5089;
                      FStar_Syntax_Syntax.actions = uu____5099;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___539_5088.FStar_Syntax_Syntax.eff_attrs)
                    }))))))))
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____5154 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____5154
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____5176 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5176
         then
           let uu____5181 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5181
         else ());
        (let uu____5187 =
           let uu____5192 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5192 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5216 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5216  in
               let uu____5217 =
                 let uu____5224 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5224 bs  in
               (match uu____5217 with
                | (bs1,uu____5230,uu____5231) ->
                    let uu____5232 =
                      let tmp_t =
                        let uu____5242 =
                          let uu____5245 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5250  ->
                                 FStar_Pervasives_Native.Some _5250)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5245
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5242  in
                      let uu____5251 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5251 with
                      | (us,tmp_t1) ->
                          let uu____5268 =
                            let uu____5269 =
                              let uu____5270 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5270
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5269
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5268)
                       in
                    (match uu____5232 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5339 ->
                              let uu____5342 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5349 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5349 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5342
                              then (us, bs2)
                              else
                                (let uu____5360 =
                                   let uu____5366 =
                                     let uu____5368 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5370 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5368 uu____5370
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5366)
                                    in
                                 let uu____5374 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5360
                                   uu____5374))))
            in
         match uu____5187 with
         | (us,bs) ->
             let ed1 =
               let uu___572_5382 = ed  in
               {
                 FStar_Syntax_Syntax.is_layered =
                   (uu___572_5382.FStar_Syntax_Syntax.is_layered);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___572_5382.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.mname =
                   (uu___572_5382.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___572_5382.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.ret_wp =
                   (uu___572_5382.FStar_Syntax_Syntax.ret_wp);
                 FStar_Syntax_Syntax.bind_wp =
                   (uu___572_5382.FStar_Syntax_Syntax.bind_wp);
                 FStar_Syntax_Syntax.stronger =
                   (uu___572_5382.FStar_Syntax_Syntax.stronger);
                 FStar_Syntax_Syntax.match_wps =
                   (uu___572_5382.FStar_Syntax_Syntax.match_wps);
                 FStar_Syntax_Syntax.trivial =
                   (uu___572_5382.FStar_Syntax_Syntax.trivial);
                 FStar_Syntax_Syntax.repr =
                   (uu___572_5382.FStar_Syntax_Syntax.repr);
                 FStar_Syntax_Syntax.return_repr =
                   (uu___572_5382.FStar_Syntax_Syntax.return_repr);
                 FStar_Syntax_Syntax.bind_repr =
                   (uu___572_5382.FStar_Syntax_Syntax.bind_repr);
                 FStar_Syntax_Syntax.stronger_repr =
                   (uu___572_5382.FStar_Syntax_Syntax.stronger_repr);
                 FStar_Syntax_Syntax.actions =
                   (uu___572_5382.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___572_5382.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5383 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5383 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5402 =
                    let uu____5407 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5407  in
                  (match uu____5402 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5428 =
                           match uu____5428 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5448 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5448 t  in
                               let uu____5457 =
                                 let uu____5458 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5458 t1  in
                               (us1, uu____5457)
                            in
                         let uu___586_5463 = ed1  in
                         let uu____5464 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5465 = op ed1.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____5466 = op ed1.FStar_Syntax_Syntax.bind_wp
                            in
                         let uu____5467 = op ed1.FStar_Syntax_Syntax.stronger
                            in
                         let uu____5468 =
                           FStar_Syntax_Util.map_match_wps op
                             ed1.FStar_Syntax_Syntax.match_wps
                            in
                         let uu____5473 =
                           FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                             op
                            in
                         let uu____5476 = op ed1.FStar_Syntax_Syntax.repr  in
                         let uu____5477 =
                           op ed1.FStar_Syntax_Syntax.return_repr  in
                         let uu____5478 =
                           op ed1.FStar_Syntax_Syntax.bind_repr  in
                         let uu____5479 =
                           FStar_List.map
                             (fun a  ->
                                let uu___589_5487 = a  in
                                let uu____5488 =
                                  let uu____5489 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5489  in
                                let uu____5500 =
                                  let uu____5501 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5501  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___589_5487.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___589_5487.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___589_5487.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___589_5487.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5488;
                                  FStar_Syntax_Syntax.action_typ = uu____5500
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.is_layered =
                             (uu___586_5463.FStar_Syntax_Syntax.is_layered);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___586_5463.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.mname =
                             (uu___586_5463.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.univs =
                             (uu___586_5463.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___586_5463.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5464;
                           FStar_Syntax_Syntax.ret_wp = uu____5465;
                           FStar_Syntax_Syntax.bind_wp = uu____5466;
                           FStar_Syntax_Syntax.stronger = uu____5467;
                           FStar_Syntax_Syntax.match_wps = uu____5468;
                           FStar_Syntax_Syntax.trivial = uu____5473;
                           FStar_Syntax_Syntax.repr = uu____5476;
                           FStar_Syntax_Syntax.return_repr = uu____5477;
                           FStar_Syntax_Syntax.bind_repr = uu____5478;
                           FStar_Syntax_Syntax.stronger_repr =
                             FStar_Pervasives_Native.None;
                           FStar_Syntax_Syntax.actions = uu____5479;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___586_5463.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5513 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5513
                         then
                           let uu____5518 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5518
                         else ());
                        (let env =
                           let uu____5525 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5525
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5560 k =
                           match uu____5560 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5580 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5580 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5589 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          tc_check_trivial_guard uu____5589
                                            t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5590 =
                                            let uu____5597 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5597 t1
                                             in
                                          (match uu____5590 with
                                           | (t2,uu____5599,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5602 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5602 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5618 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5620 =
                                                 let uu____5622 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5622
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5618 uu____5620
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5637 ->
                                               let uu____5638 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5645 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5645 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5638
                                               then (g_us, t3)
                                               else
                                                 (let uu____5656 =
                                                    let uu____5662 =
                                                      let uu____5664 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5666 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5664
                                                        uu____5666
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5662)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5656
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5674 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5674
                          then
                            let uu____5679 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5679
                          else ());
                         (let fresh_a_and_wp uu____5695 =
                            let fail1 t =
                              let uu____5708 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5708
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5724 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5724 with
                            | (uu____5735,signature1) ->
                                let uu____5737 =
                                  let uu____5738 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5738.FStar_Syntax_Syntax.n  in
                                (match uu____5737 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5748) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5777)::(wp,uu____5779)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5808 -> fail1 signature1)
                                 | uu____5809 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5823 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5823
                            then
                              let uu____5828 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____5828
                            else ()  in
                          let ret_wp =
                            let uu____5834 = fresh_a_and_wp ()  in
                            match uu____5834 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5850 =
                                    let uu____5859 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5866 =
                                      let uu____5875 =
                                        let uu____5882 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5882
                                         in
                                      [uu____5875]  in
                                    uu____5859 :: uu____5866  in
                                  let uu____5901 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5850
                                    uu____5901
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None
                                  ed2.FStar_Syntax_Syntax.ret_wp
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5909 = fresh_a_and_wp ()  in
                             match uu____5909 with
                             | (a,wp_sort_a) ->
                                 let uu____5922 = fresh_a_and_wp ()  in
                                 (match uu____5922 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5938 =
                                          let uu____5947 =
                                            let uu____5954 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5954
                                             in
                                          [uu____5947]  in
                                        let uu____5967 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5938
                                          uu____5967
                                         in
                                      let k =
                                        let uu____5973 =
                                          let uu____5982 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5989 =
                                            let uu____5998 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____6005 =
                                              let uu____6014 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____6021 =
                                                let uu____6030 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____6037 =
                                                  let uu____6046 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6046]  in
                                                uu____6030 :: uu____6037  in
                                              uu____6014 :: uu____6021  in
                                            uu____5998 :: uu____6005  in
                                          uu____5982 :: uu____5989  in
                                        let uu____6089 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5973
                                          uu____6089
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6097 = fresh_a_and_wp ()  in
                              match uu____6097 with
                              | (a,wp_sort_a) ->
                                  let uu____6110 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6110 with
                                   | (t,uu____6116) ->
                                       let k =
                                         let uu____6120 =
                                           let uu____6129 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6136 =
                                             let uu____6145 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6152 =
                                               let uu____6161 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6161]  in
                                             uu____6145 :: uu____6152  in
                                           uu____6129 :: uu____6136  in
                                         let uu____6192 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6120
                                           uu____6192
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         ed2.FStar_Syntax_Syntax.stronger
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let match_wps =
                               let uu____6204 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   ed2.FStar_Syntax_Syntax.match_wps
                                  in
                               match uu____6204 with
                               | (if_then_else1,ite_wp,close_wp) ->
                                   let if_then_else2 =
                                     let uu____6219 = fresh_a_and_wp ()  in
                                     match uu____6219 with
                                     | (a,wp_sort_a) ->
                                         let p =
                                           let uu____6233 =
                                             let uu____6236 =
                                               FStar_Ident.range_of_lid
                                                 ed2.FStar_Syntax_Syntax.mname
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____6236
                                              in
                                           let uu____6237 =
                                             let uu____6238 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_right uu____6238
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____6233 uu____6237
                                            in
                                         let k =
                                           let uu____6250 =
                                             let uu____6259 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____6266 =
                                               let uu____6275 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   p
                                                  in
                                               let uu____6282 =
                                                 let uu____6291 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 let uu____6298 =
                                                   let uu____6307 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       wp_sort_a
                                                      in
                                                   [uu____6307]  in
                                                 uu____6291 :: uu____6298  in
                                               uu____6275 :: uu____6282  in
                                             uu____6259 :: uu____6266  in
                                           let uu____6344 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____6250
                                             uu____6344
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
                                       let uu____6352 = fresh_a_and_wp ()  in
                                       match uu____6352 with
                                       | (a,wp_sort_a) ->
                                           let k =
                                             let uu____6368 =
                                               let uu____6377 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6384 =
                                                 let uu____6393 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6393]  in
                                               uu____6377 :: uu____6384  in
                                             let uu____6418 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 wp_sort_a
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6368 uu____6418
                                              in
                                           check_and_gen' "ite_wp"
                                             Prims.int_one
                                             FStar_Pervasives_Native.None
                                             ite_wp
                                             (FStar_Pervasives_Native.Some k)
                                        in
                                     log_combinator "ite_wp" ite_wp1;
                                     (let close_wp1 =
                                        let uu____6426 = fresh_a_and_wp ()
                                           in
                                        match uu____6426 with
                                        | (a,wp_sort_a) ->
                                            let b =
                                              let uu____6440 =
                                                let uu____6443 =
                                                  FStar_Ident.range_of_lid
                                                    ed2.FStar_Syntax_Syntax.mname
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____6443
                                                 in
                                              let uu____6444 =
                                                let uu____6445 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____6445
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.new_bv
                                                uu____6440 uu____6444
                                               in
                                            let wp_sort_b_a =
                                              let uu____6457 =
                                                let uu____6466 =
                                                  let uu____6473 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      b
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____6473
                                                   in
                                                [uu____6466]  in
                                              let uu____6486 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____6457 uu____6486
                                               in
                                            let k =
                                              let uu____6492 =
                                                let uu____6501 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____6508 =
                                                  let uu____6517 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____6524 =
                                                    let uu____6533 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_b_a
                                                       in
                                                    [uu____6533]  in
                                                  uu____6517 :: uu____6524
                                                   in
                                                uu____6501 :: uu____6508  in
                                              let uu____6564 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____6492 uu____6564
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
                               let uu____6574 = fresh_a_and_wp ()  in
                               match uu____6574 with
                               | (a,wp_sort_a) ->
                                   let uu____6589 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____6589 with
                                    | (t,uu____6597) ->
                                        let k =
                                          let uu____6601 =
                                            let uu____6610 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____6617 =
                                              let uu____6626 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              [uu____6626]  in
                                            uu____6610 :: uu____6617  in
                                          let uu____6651 =
                                            FStar_Syntax_Syntax.mk_GTotal t
                                             in
                                          FStar_Syntax_Util.arrow uu____6601
                                            uu____6651
                                           in
                                        let trivial =
                                          let uu____6655 =
                                            FStar_All.pipe_right
                                              ed2.FStar_Syntax_Syntax.trivial
                                              FStar_Util.must
                                             in
                                          check_and_gen' "trivial"
                                            Prims.int_one
                                            FStar_Pervasives_Native.None
                                            uu____6655
                                            (FStar_Pervasives_Native.Some k)
                                           in
                                        (log_combinator "trivial" trivial;
                                         FStar_Pervasives_Native.Some trivial))
                                in
                             let uu____6670 =
                               let uu____6681 =
                                 let uu____6682 =
                                   FStar_Syntax_Subst.compress
                                     (FStar_Pervasives_Native.snd
                                        ed2.FStar_Syntax_Syntax.repr)
                                    in
                                 uu____6682.FStar_Syntax_Syntax.n  in
                               match uu____6681 with
                               | FStar_Syntax_Syntax.Tm_unknown  ->
                                   ((ed2.FStar_Syntax_Syntax.repr),
                                     (ed2.FStar_Syntax_Syntax.return_repr),
                                     (ed2.FStar_Syntax_Syntax.bind_repr),
                                     (ed2.FStar_Syntax_Syntax.actions))
                               | uu____6701 ->
                                   let repr =
                                     let uu____6703 = fresh_a_and_wp ()  in
                                     match uu____6703 with
                                     | (a,wp_sort_a) ->
                                         let uu____6716 =
                                           FStar_Syntax_Util.type_u ()  in
                                         (match uu____6716 with
                                          | (t,uu____6722) ->
                                              let k =
                                                let uu____6726 =
                                                  let uu____6735 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____6742 =
                                                    let uu____6751 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a
                                                       in
                                                    [uu____6751]  in
                                                  uu____6735 :: uu____6742
                                                   in
                                                let uu____6776 =
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____6726 uu____6776
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
                                       let uu____6796 =
                                         FStar_TypeChecker_Env.inst_tscheme
                                           repr
                                          in
                                       match uu____6796 with
                                       | (uu____6803,repr1) ->
                                           let repr2 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.EraseUniverses;
                                               FStar_TypeChecker_Env.AllowUnboundUniverses]
                                               env repr1
                                              in
                                           let uu____6806 =
                                             let uu____6813 =
                                               let uu____6814 =
                                                 let uu____6831 =
                                                   let uu____6842 =
                                                     FStar_All.pipe_right t
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   let uu____6859 =
                                                     let uu____6870 =
                                                       FStar_All.pipe_right
                                                         wp
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____6870]  in
                                                   uu____6842 :: uu____6859
                                                    in
                                                 (repr2, uu____6831)  in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____6814
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____6813
                                              in
                                           uu____6806
                                             FStar_Pervasives_Native.None
                                             FStar_Range.dummyRange
                                        in
                                     let mk_repr a wp =
                                       let uu____6936 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_repr' uu____6936 wp  in
                                     let destruct_repr t =
                                       let uu____6951 =
                                         let uu____6952 =
                                           FStar_Syntax_Subst.compress t  in
                                         uu____6952.FStar_Syntax_Syntax.n  in
                                       match uu____6951 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____6963,(t1,uu____6965)::
                                            (wp,uu____6967)::[])
                                           -> (t1, wp)
                                       | uu____7026 ->
                                           failwith "Unexpected repr type"
                                        in
                                     let return_repr =
                                       let uu____7037 = fresh_a_and_wp ()  in
                                       match uu____7037 with
                                       | (a,uu____7045) ->
                                           let x_a =
                                             let uu____7051 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             FStar_Syntax_Syntax.gen_bv "x_a"
                                               FStar_Pervasives_Native.None
                                               uu____7051
                                              in
                                           let res =
                                             let wp =
                                               let uu____7059 =
                                                 let uu____7064 =
                                                   let uu____7065 =
                                                     FStar_TypeChecker_Env.inst_tscheme
                                                       ret_wp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____7065
                                                     FStar_Pervasives_Native.snd
                                                    in
                                                 let uu____7074 =
                                                   let uu____7075 =
                                                     let uu____7084 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____7084
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   let uu____7093 =
                                                     let uu____7104 =
                                                       let uu____7113 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____7113
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____7104]  in
                                                   uu____7075 :: uu____7093
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   uu____7064 uu____7074
                                                  in
                                               uu____7059
                                                 FStar_Pervasives_Native.None
                                                 FStar_Range.dummyRange
                                                in
                                             mk_repr a wp  in
                                           let k =
                                             let uu____7149 =
                                               let uu____7158 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____7165 =
                                                 let uu____7174 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x_a
                                                    in
                                                 [uu____7174]  in
                                               uu____7158 :: uu____7165  in
                                             let uu____7199 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 res
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____7149 uu____7199
                                              in
                                           let uu____7202 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env k
                                              in
                                           (match uu____7202 with
                                            | (k1,uu____7210,uu____7211) ->
                                                let env1 =
                                                  let uu____7215 =
                                                    FStar_TypeChecker_Env.set_range
                                                      env
                                                      (FStar_Pervasives_Native.snd
                                                         ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____7215
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
                                          let uu____7226 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____7226
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____7227 = fresh_a_and_wp ()
                                           in
                                        match uu____7227 with
                                        | (a,wp_sort_a) ->
                                            let uu____7240 =
                                              fresh_a_and_wp ()  in
                                            (match uu____7240 with
                                             | (b,wp_sort_b) ->
                                                 let wp_sort_a_b =
                                                   let uu____7256 =
                                                     let uu____7265 =
                                                       let uu____7272 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a
                                                          in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____7272
                                                        in
                                                     [uu____7265]  in
                                                   let uu____7285 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       wp_sort_b
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____7256 uu____7285
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
                                                   let uu____7293 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "x_a"
                                                     FStar_Pervasives_Native.None
                                                     uu____7293
                                                    in
                                                 let wp_g_x =
                                                   let uu____7298 =
                                                     let uu____7303 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_g
                                                        in
                                                     let uu____7304 =
                                                       let uu____7305 =
                                                         let uu____7314 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x_a
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____7314
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____7305]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____7303 uu____7304
                                                      in
                                                   uu____7298
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 let res =
                                                   let wp =
                                                     let uu____7345 =
                                                       let uu____7350 =
                                                         let uu____7351 =
                                                           FStar_TypeChecker_Env.inst_tscheme
                                                             bind_wp
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____7351
                                                           FStar_Pervasives_Native.snd
                                                          in
                                                       let uu____7360 =
                                                         let uu____7361 =
                                                           let uu____7364 =
                                                             let uu____7367 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 a
                                                                in
                                                             let uu____7368 =
                                                               let uu____7371
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   b
                                                                  in
                                                               let uu____7372
                                                                 =
                                                                 let uu____7375
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                    in
                                                                 let uu____7376
                                                                   =
                                                                   let uu____7379
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                   [uu____7379]
                                                                    in
                                                                 uu____7375
                                                                   ::
                                                                   uu____7376
                                                                  in
                                                               uu____7371 ::
                                                                 uu____7372
                                                                in
                                                             uu____7367 ::
                                                               uu____7368
                                                              in
                                                           r :: uu____7364
                                                            in
                                                         FStar_List.map
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____7361
                                                          in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____7350
                                                         uu____7360
                                                        in
                                                     uu____7345
                                                       FStar_Pervasives_Native.None
                                                       FStar_Range.dummyRange
                                                      in
                                                   mk_repr b wp  in
                                                 let maybe_range_arg =
                                                   let uu____7397 =
                                                     FStar_Util.for_some
                                                       (FStar_Syntax_Util.attr_eq
                                                          FStar_Syntax_Util.dm4f_bind_range_attr)
                                                       ed2.FStar_Syntax_Syntax.eff_attrs
                                                      in
                                                   if uu____7397
                                                   then
                                                     let uu____7408 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     let uu____7415 =
                                                       let uu____7424 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           FStar_Syntax_Syntax.t_range
                                                          in
                                                       [uu____7424]  in
                                                     uu____7408 :: uu____7415
                                                   else []  in
                                                 let k =
                                                   let uu____7460 =
                                                     let uu____7469 =
                                                       let uu____7478 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           a
                                                          in
                                                       let uu____7485 =
                                                         let uu____7494 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             b
                                                            in
                                                         [uu____7494]  in
                                                       uu____7478 ::
                                                         uu____7485
                                                        in
                                                     let uu____7519 =
                                                       let uu____7528 =
                                                         let uu____7537 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             wp_f
                                                            in
                                                         let uu____7544 =
                                                           let uu____7553 =
                                                             let uu____7560 =
                                                               let uu____7561
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               mk_repr a
                                                                 uu____7561
                                                                in
                                                             FStar_Syntax_Syntax.null_binder
                                                               uu____7560
                                                              in
                                                           let uu____7562 =
                                                             let uu____7571 =
                                                               FStar_Syntax_Syntax.mk_binder
                                                                 wp_g
                                                                in
                                                             let uu____7578 =
                                                               let uu____7587
                                                                 =
                                                                 let uu____7594
                                                                   =
                                                                   let uu____7595
                                                                    =
                                                                    let uu____7604
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7604]
                                                                     in
                                                                   let uu____7623
                                                                    =
                                                                    let uu____7626
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7626
                                                                     in
                                                                   FStar_Syntax_Util.arrow
                                                                    uu____7595
                                                                    uu____7623
                                                                    in
                                                                 FStar_Syntax_Syntax.null_binder
                                                                   uu____7594
                                                                  in
                                                               [uu____7587]
                                                                in
                                                             uu____7571 ::
                                                               uu____7578
                                                              in
                                                           uu____7553 ::
                                                             uu____7562
                                                            in
                                                         uu____7537 ::
                                                           uu____7544
                                                          in
                                                       FStar_List.append
                                                         maybe_range_arg
                                                         uu____7528
                                                        in
                                                     FStar_List.append
                                                       uu____7469 uu____7519
                                                      in
                                                   let uu____7671 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       res
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____7460 uu____7671
                                                    in
                                                 let uu____7674 =
                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                     env k
                                                    in
                                                 (match uu____7674 with
                                                  | (k1,uu____7682,uu____7683)
                                                      ->
                                                      let env1 =
                                                        FStar_TypeChecker_Env.set_range
                                                          env
                                                          (FStar_Pervasives_Native.snd
                                                             ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                         in
                                                      let env2 =
                                                        FStar_All.pipe_right
                                                          (let uu___787_7695
                                                             = env1  in
                                                           {
                                                             FStar_TypeChecker_Env.solver
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.solver);
                                                             FStar_TypeChecker_Env.range
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.range);
                                                             FStar_TypeChecker_Env.curmodule
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.curmodule);
                                                             FStar_TypeChecker_Env.gamma
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.gamma);
                                                             FStar_TypeChecker_Env.gamma_sig
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.gamma_sig);
                                                             FStar_TypeChecker_Env.gamma_cache
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.gamma_cache);
                                                             FStar_TypeChecker_Env.modules
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.modules);
                                                             FStar_TypeChecker_Env.expected_typ
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.expected_typ);
                                                             FStar_TypeChecker_Env.sigtab
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.sigtab);
                                                             FStar_TypeChecker_Env.attrtab
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.attrtab);
                                                             FStar_TypeChecker_Env.instantiate_imp
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.instantiate_imp);
                                                             FStar_TypeChecker_Env.effects
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.effects);
                                                             FStar_TypeChecker_Env.generalize
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.generalize);
                                                             FStar_TypeChecker_Env.letrecs
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.letrecs);
                                                             FStar_TypeChecker_Env.top_level
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.top_level);
                                                             FStar_TypeChecker_Env.check_uvars
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.check_uvars);
                                                             FStar_TypeChecker_Env.use_eq
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.use_eq);
                                                             FStar_TypeChecker_Env.is_iface
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.is_iface);
                                                             FStar_TypeChecker_Env.admit
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.admit);
                                                             FStar_TypeChecker_Env.lax
                                                               = true;
                                                             FStar_TypeChecker_Env.lax_universes
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.lax_universes);
                                                             FStar_TypeChecker_Env.phase1
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.phase1);
                                                             FStar_TypeChecker_Env.failhard
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.failhard);
                                                             FStar_TypeChecker_Env.nosynth
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.nosynth);
                                                             FStar_TypeChecker_Env.uvar_subtyping
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.uvar_subtyping);
                                                             FStar_TypeChecker_Env.tc_term
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.tc_term);
                                                             FStar_TypeChecker_Env.type_of
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.type_of);
                                                             FStar_TypeChecker_Env.universe_of
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.universe_of);
                                                             FStar_TypeChecker_Env.check_type_of
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.check_type_of);
                                                             FStar_TypeChecker_Env.use_bv_sorts
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.use_bv_sorts);
                                                             FStar_TypeChecker_Env.qtbl_name_and_index
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                             FStar_TypeChecker_Env.normalized_eff_names
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.normalized_eff_names);
                                                             FStar_TypeChecker_Env.fv_delta_depths
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.fv_delta_depths);
                                                             FStar_TypeChecker_Env.proof_ns
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.proof_ns);
                                                             FStar_TypeChecker_Env.synth_hook
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.synth_hook);
                                                             FStar_TypeChecker_Env.splice
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.splice);
                                                             FStar_TypeChecker_Env.mpreprocess
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.mpreprocess);
                                                             FStar_TypeChecker_Env.postprocess
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.postprocess);
                                                             FStar_TypeChecker_Env.is_native_tactic
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.is_native_tactic);
                                                             FStar_TypeChecker_Env.identifier_info
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.identifier_info);
                                                             FStar_TypeChecker_Env.tc_hooks
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.tc_hooks);
                                                             FStar_TypeChecker_Env.dsenv
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.dsenv);
                                                             FStar_TypeChecker_Env.nbe
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.nbe);
                                                             FStar_TypeChecker_Env.strict_args_tab
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.strict_args_tab);
                                                             FStar_TypeChecker_Env.erasable_types_tab
                                                               =
                                                               (uu___787_7695.FStar_TypeChecker_Env.erasable_types_tab)
                                                           })
                                                          (fun _7697  ->
                                                             FStar_Pervasives_Native.Some
                                                               _7697)
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
                                           (let uu____7724 =
                                              if
                                                act.FStar_Syntax_Syntax.action_univs
                                                  = []
                                              then (env, act)
                                              else
                                                (let uu____7738 =
                                                   FStar_Syntax_Subst.univ_var_opening
                                                     act.FStar_Syntax_Syntax.action_univs
                                                    in
                                                 match uu____7738 with
                                                 | (usubst,uvs) ->
                                                     let uu____7761 =
                                                       FStar_TypeChecker_Env.push_univ_vars
                                                         env uvs
                                                        in
                                                     let uu____7762 =
                                                       let uu___800_7763 =
                                                         act  in
                                                       let uu____7764 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____7765 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___800_7763.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___800_7763.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = uvs;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___800_7763.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = uu____7764;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____7765
                                                       }  in
                                                     (uu____7761, uu____7762))
                                               in
                                            match uu____7724 with
                                            | (env1,act1) ->
                                                let act_typ =
                                                  let uu____7769 =
                                                    let uu____7770 =
                                                      FStar_Syntax_Subst.compress
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                       in
                                                    uu____7770.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____7769 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs1,c) ->
                                                      let c1 =
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                          c
                                                         in
                                                      let uu____7796 =
                                                        FStar_Ident.lid_equals
                                                          c1.FStar_Syntax_Syntax.effect_name
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      if uu____7796
                                                      then
                                                        let uu____7799 =
                                                          let uu____7802 =
                                                            let uu____7803 =
                                                              let uu____7804
                                                                =
                                                                FStar_List.hd
                                                                  c1.FStar_Syntax_Syntax.effect_args
                                                                 in
                                                              FStar_Pervasives_Native.fst
                                                                uu____7804
                                                               in
                                                            mk_repr'
                                                              c1.FStar_Syntax_Syntax.result_typ
                                                              uu____7803
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total
                                                            uu____7802
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          bs1 uu____7799
                                                      else
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                  | uu____7827 ->
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                   in
                                                let uu____7828 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env1 act_typ
                                                   in
                                                (match uu____7828 with
                                                 | (act_typ1,uu____7836,g_t)
                                                     ->
                                                     let env' =
                                                       let uu___817_7839 =
                                                         FStar_TypeChecker_Env.set_expected_typ
                                                           env1 act_typ1
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           = false;
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.lax);
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.mpreprocess
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.mpreprocess);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.nbe);
                                                         FStar_TypeChecker_Env.strict_args_tab
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.strict_args_tab);
                                                         FStar_TypeChecker_Env.erasable_types_tab
                                                           =
                                                           (uu___817_7839.FStar_TypeChecker_Env.erasable_types_tab)
                                                       }  in
                                                     ((let uu____7842 =
                                                         FStar_TypeChecker_Env.debug
                                                           env1
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____7842
                                                       then
                                                         let uu____7846 =
                                                           FStar_Ident.text_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name
                                                            in
                                                         let uu____7848 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____7850 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act_typ1
                                                            in
                                                         FStar_Util.print3
                                                           "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                           uu____7846
                                                           uu____7848
                                                           uu____7850
                                                       else ());
                                                      (let uu____7855 =
                                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                           env'
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       match uu____7855 with
                                                       | (act_defn,uu____7863,g_a)
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
                                                           let uu____7867 =
                                                             let act_typ3 =
                                                               FStar_Syntax_Subst.compress
                                                                 act_typ2
                                                                in
                                                             match act_typ3.FStar_Syntax_Syntax.n
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs1,c) ->
                                                                 let uu____7903
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs1 c
                                                                    in
                                                                 (match uu____7903
                                                                  with
                                                                  | (bs2,uu____7915)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____7922
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7922
                                                                     in
                                                                    let uu____7925
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____7925
                                                                    with
                                                                    | 
                                                                    (k1,uu____7939,g)
                                                                    ->
                                                                    (k1, g)))
                                                             | uu____7943 ->
                                                                 let uu____7944
                                                                   =
                                                                   let uu____7950
                                                                    =
                                                                    let uu____7952
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____7954
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____7952
                                                                    uu____7954
                                                                     in
                                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____7950)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____7944
                                                                   act_defn1.FStar_Syntax_Syntax.pos
                                                              in
                                                           (match uu____7867
                                                            with
                                                            | (expected_k,g_k)
                                                                ->
                                                                let g =
                                                                  FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k
                                                                   in
                                                                ((let uu____7972
                                                                    =
                                                                    let uu____7973
                                                                    =
                                                                    let uu____7974
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____7974
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____7973
                                                                     in
                                                                  FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____7972);
                                                                 (let act_typ3
                                                                    =
                                                                    let uu____7976
                                                                    =
                                                                    let uu____7977
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____7977.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____7976
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8002
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8002
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8009
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8009
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8029
                                                                    =
                                                                    let uu____8030
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8030]
                                                                     in
                                                                    let uu____8031
                                                                    =
                                                                    let uu____8042
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8042]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8029;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8031;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8067
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8067))
                                                                    | 
                                                                    uu____8070
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                  let uu____8072
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8094
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8094))
                                                                     in
                                                                  match uu____8072
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
                                                                    let uu___867_8113
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___867_8113.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___867_8113.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___867_8113.FStar_Syntax_Syntax.action_params);
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
                             match uu____6670 with
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
                                   let uu____8138 =
                                     FStar_Syntax_Subst.shift_subst
                                       (FStar_List.length ed_bs)
                                       ed_univs_closing
                                      in
                                   FStar_Syntax_Subst.subst_tscheme
                                     uu____8138 ts1
                                    in
                                 let ed3 =
                                   let uu___879_8148 = ed2  in
                                   let uu____8149 = cl signature  in
                                   let uu____8150 = cl ret_wp  in
                                   let uu____8151 = cl bind_wp  in
                                   let uu____8152 = cl stronger  in
                                   let uu____8153 =
                                     FStar_Syntax_Util.map_match_wps cl
                                       match_wps
                                      in
                                   let uu____8158 =
                                     FStar_Util.map_opt trivial cl  in
                                   let uu____8161 = cl repr  in
                                   let uu____8162 = cl return_repr  in
                                   let uu____8163 = cl bind_repr  in
                                   let uu____8164 =
                                     FStar_List.map
                                       (fun a  ->
                                          let uu___882_8172 = a  in
                                          let uu____8173 =
                                            let uu____8174 =
                                              cl
                                                ((a.FStar_Syntax_Syntax.action_univs),
                                                  (a.FStar_Syntax_Syntax.action_defn))
                                               in
                                            FStar_All.pipe_right uu____8174
                                              FStar_Pervasives_Native.snd
                                             in
                                          let uu____8199 =
                                            let uu____8200 =
                                              cl
                                                ((a.FStar_Syntax_Syntax.action_univs),
                                                  (a.FStar_Syntax_Syntax.action_typ))
                                               in
                                            FStar_All.pipe_right uu____8200
                                              FStar_Pervasives_Native.snd
                                             in
                                          {
                                            FStar_Syntax_Syntax.action_name =
                                              (uu___882_8172.FStar_Syntax_Syntax.action_name);
                                            FStar_Syntax_Syntax.action_unqualified_name
                                              =
                                              (uu___882_8172.FStar_Syntax_Syntax.action_unqualified_name);
                                            FStar_Syntax_Syntax.action_univs
                                              =
                                              (uu___882_8172.FStar_Syntax_Syntax.action_univs);
                                            FStar_Syntax_Syntax.action_params
                                              =
                                              (uu___882_8172.FStar_Syntax_Syntax.action_params);
                                            FStar_Syntax_Syntax.action_defn =
                                              uu____8173;
                                            FStar_Syntax_Syntax.action_typ =
                                              uu____8199
                                          }) actions
                                      in
                                   {
                                     FStar_Syntax_Syntax.is_layered =
                                       (uu___879_8148.FStar_Syntax_Syntax.is_layered);
                                     FStar_Syntax_Syntax.cattributes =
                                       (uu___879_8148.FStar_Syntax_Syntax.cattributes);
                                     FStar_Syntax_Syntax.mname =
                                       (uu___879_8148.FStar_Syntax_Syntax.mname);
                                     FStar_Syntax_Syntax.univs =
                                       (uu___879_8148.FStar_Syntax_Syntax.univs);
                                     FStar_Syntax_Syntax.binders =
                                       (uu___879_8148.FStar_Syntax_Syntax.binders);
                                     FStar_Syntax_Syntax.signature =
                                       uu____8149;
                                     FStar_Syntax_Syntax.ret_wp = uu____8150;
                                     FStar_Syntax_Syntax.bind_wp = uu____8151;
                                     FStar_Syntax_Syntax.stronger =
                                       uu____8152;
                                     FStar_Syntax_Syntax.match_wps =
                                       uu____8153;
                                     FStar_Syntax_Syntax.trivial = uu____8158;
                                     FStar_Syntax_Syntax.repr = uu____8161;
                                     FStar_Syntax_Syntax.return_repr =
                                       uu____8162;
                                     FStar_Syntax_Syntax.bind_repr =
                                       uu____8163;
                                     FStar_Syntax_Syntax.stronger_repr =
                                       FStar_Pervasives_Native.None;
                                     FStar_Syntax_Syntax.actions = uu____8164;
                                     FStar_Syntax_Syntax.eff_attrs =
                                       (uu___879_8148.FStar_Syntax_Syntax.eff_attrs)
                                   }  in
                                 ((let uu____8226 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "ED")
                                      in
                                   if uu____8226
                                   then
                                     let uu____8231 =
                                       FStar_Syntax_Print.eff_decl_to_string
                                         false ed3
                                        in
                                     FStar_Util.print1
                                       "Typechecked effect declaration:\n\t%s\n"
                                       uu____8231
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
        let fail1 uu____8296 =
          let uu____8297 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8303 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8297 uu____8303  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8347)::(wp,uu____8349)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8378 -> fail1 ())
        | uu____8379 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8392 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8392
       then
         let uu____8397 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8397
       else ());
      (let uu____8402 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____8402 with
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
             let uu____8435 =
               ((FStar_Pervasives_Native.fst
                   src_ed.FStar_Syntax_Syntax.is_layered)
                  &&
                  (let uu____8441 =
                     let uu____8442 =
                       FStar_All.pipe_right
                         src_ed.FStar_Syntax_Syntax.is_layered
                         FStar_Pervasives_Native.snd
                        in
                     FStar_All.pipe_right uu____8442 FStar_Util.must  in
                   FStar_Ident.lid_equals uu____8441
                     tgt_ed.FStar_Syntax_Syntax.mname))
                 ||
                 (((FStar_Pervasives_Native.fst
                      tgt_ed.FStar_Syntax_Syntax.is_layered)
                     &&
                     (let uu____8463 =
                        let uu____8464 =
                          FStar_All.pipe_right
                            tgt_ed.FStar_Syntax_Syntax.is_layered
                            FStar_Pervasives_Native.snd
                           in
                        FStar_All.pipe_right uu____8464 FStar_Util.must  in
                      FStar_Ident.lid_equals uu____8463
                        src_ed.FStar_Syntax_Syntax.mname))
                    &&
                    (let uu____8482 =
                       FStar_Ident.lid_equals
                         src_ed.FStar_Syntax_Syntax.mname
                         FStar_Parser_Const.effect_PURE_lid
                        in
                     Prims.op_Negation uu____8482))
                in
             if uu____8435
             then
               let uu____8485 =
                 let uu____8491 =
                   let uu____8493 =
                     FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   let uu____8496 =
                     FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   FStar_Util.format2
                     "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                     uu____8493 uu____8496
                    in
                 (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8491)  in
               FStar_Errors.raise_error uu____8485 r
             else ());
            (let uu____8503 =
               if (FStar_List.length us) = Prims.int_zero
               then (env0, us, lift)
               else
                 (let uu____8527 = FStar_Syntax_Subst.open_univ_vars us lift
                     in
                  match uu____8527 with
                  | (us1,lift1) ->
                      let uu____8542 =
                        FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                      (uu____8542, us1, lift1))
                in
             match uu____8503 with
             | (env,us1,lift1) ->
                 let uu____8552 =
                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                 (match uu____8552 with
                  | (lift2,lc,g) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env g;
                       (let lift_ty =
                          FStar_All.pipe_right
                            lc.FStar_TypeChecker_Common.res_typ
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta] env0)
                           in
                        (let uu____8565 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "LayeredEffects")
                            in
                         if uu____8565
                         then
                           let uu____8570 =
                             FStar_Syntax_Print.term_to_string lift2  in
                           let uu____8572 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.print2
                             "Typechecked lift: %s and lift_ty: %s\n"
                             uu____8570 uu____8572
                         else ());
                        (let lift_t_shape_error s =
                           let uu____8586 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.source
                              in
                           let uu____8588 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.target
                              in
                           let uu____8590 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.format4
                             "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                             uu____8586 uu____8588 s uu____8590
                            in
                         let uu____8593 =
                           let uu____8600 =
                             let uu____8605 = FStar_Syntax_Util.type_u ()  in
                             FStar_All.pipe_right uu____8605
                               (fun uu____8622  ->
                                  match uu____8622 with
                                  | (t,u) ->
                                      let uu____8633 =
                                        let uu____8634 =
                                          FStar_Syntax_Syntax.gen_bv "a"
                                            FStar_Pervasives_Native.None t
                                           in
                                        FStar_All.pipe_right uu____8634
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____8633, u))
                              in
                           match uu____8600 with
                           | (a,u_a) ->
                               let rest_bs =
                                 let uu____8653 =
                                   let uu____8654 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____8654.FStar_Syntax_Syntax.n  in
                                 match uu____8653 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____8666) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____8694 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____8694 with
                                      | (a',uu____8704)::bs1 ->
                                          let uu____8724 =
                                            let uu____8725 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one))
                                               in
                                            FStar_All.pipe_right uu____8725
                                              FStar_Pervasives_Native.fst
                                             in
                                          let uu____8823 =
                                            let uu____8836 =
                                              let uu____8839 =
                                                let uu____8840 =
                                                  let uu____8847 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____8847)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____8840
                                                 in
                                              [uu____8839]  in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____8836
                                             in
                                          FStar_All.pipe_right uu____8724
                                            uu____8823)
                                 | uu____8862 ->
                                     let uu____8863 =
                                       let uu____8869 =
                                         lift_t_shape_error
                                           "either not an arrow, or not enough binders"
                                          in
                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                         uu____8869)
                                        in
                                     FStar_Errors.raise_error uu____8863 r
                                  in
                               let uu____8881 =
                                 let uu____8892 =
                                   let uu____8897 =
                                     FStar_TypeChecker_Env.push_binders env
                                       (a :: rest_bs)
                                      in
                                   let uu____8904 =
                                     let uu____8905 =
                                       FStar_All.pipe_right a
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8905
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   FStar_TypeChecker_Util.fresh_effect_repr_en
                                     uu____8897 r
                                     sub1.FStar_Syntax_Syntax.source u_a
                                     uu____8904
                                    in
                                 match uu____8892 with
                                 | (f_sort,g1) ->
                                     let uu____8926 =
                                       let uu____8933 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None
                                           f_sort
                                          in
                                       FStar_All.pipe_right uu____8933
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____8926, g1)
                                  in
                               (match uu____8881 with
                                | (f_b,g_f_b) ->
                                    let bs = a ::
                                      (FStar_List.append rest_bs [f_b])  in
                                    let uu____9000 =
                                      let uu____9005 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9006 =
                                        let uu____9007 =
                                          FStar_All.pipe_right a
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____9007
                                          FStar_Syntax_Syntax.bv_to_name
                                         in
                                      FStar_TypeChecker_Util.fresh_effect_repr_en
                                        uu____9005 r
                                        sub1.FStar_Syntax_Syntax.target u_a
                                        uu____9006
                                       in
                                    (match uu____9000 with
                                     | (repr,g_repr) ->
                                         let uu____9024 =
                                           let uu____9027 =
                                             let uu____9030 =
                                               let uu____9033 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               FStar_All.pipe_right
                                                 uu____9033
                                                 (fun _9036  ->
                                                    FStar_Pervasives_Native.Some
                                                      _9036)
                                                in
                                             FStar_Syntax_Syntax.mk_Total'
                                               repr uu____9030
                                              in
                                           FStar_Syntax_Util.arrow bs
                                             uu____9027
                                            in
                                         let uu____9037 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g_f_b g_repr
                                            in
                                         (uu____9024, uu____9037)))
                            in
                         match uu____8593 with
                         | (k,g_k) ->
                             ((let uu____9047 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____9047
                               then
                                 let uu____9052 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "tc_layered_lift: before unification k: %s\n"
                                   uu____9052
                               else ());
                              (let g1 =
                                 FStar_TypeChecker_Rel.teq env lift_ty k  in
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g_k;
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g1;
                               (let uu____9061 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____9061
                                then
                                  let uu____9066 =
                                    FStar_Syntax_Print.term_to_string k  in
                                  FStar_Util.print1
                                    "After unification k: %s\n" uu____9066
                                else ());
                               (let uu____9071 =
                                  let uu____9084 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 lift2
                                     in
                                  match uu____9084 with
                                  | (inst_us,lift3) ->
                                      (if
                                         (FStar_List.length inst_us) <>
                                           Prims.int_one
                                       then
                                         (let uu____9111 =
                                            let uu____9117 =
                                              let uu____9119 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____9121 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____9123 =
                                                let uu____9125 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____9125
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____9132 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format4
                                                "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                                uu____9119 uu____9121
                                                uu____9123 uu____9132
                                               in
                                            (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                              uu____9117)
                                             in
                                          FStar_Errors.raise_error uu____9111
                                            r)
                                       else ();
                                       (let uu____9138 =
                                          ((FStar_List.length us1) =
                                             Prims.int_zero)
                                            ||
                                            (((FStar_List.length us1) =
                                                (FStar_List.length inst_us))
                                               &&
                                               (FStar_List.forall2
                                                  (fun u1  ->
                                                     fun u2  ->
                                                       let uu____9147 =
                                                         FStar_Syntax_Syntax.order_univ_name
                                                           u1 u2
                                                          in
                                                       uu____9147 =
                                                         Prims.int_zero) us1
                                                  inst_us))
                                           in
                                        if uu____9138
                                        then
                                          let uu____9164 =
                                            let uu____9167 =
                                              FStar_All.pipe_right k
                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                   env)
                                               in
                                            FStar_All.pipe_right uu____9167
                                              (FStar_Syntax_Subst.close_univ_vars
                                                 inst_us)
                                             in
                                          (inst_us, lift3, uu____9164)
                                        else
                                          (let uu____9178 =
                                             let uu____9184 =
                                               let uu____9186 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.source
                                                  in
                                               let uu____9188 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.target
                                                  in
                                               let uu____9190 =
                                                 let uu____9192 =
                                                   FStar_All.pipe_right us1
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9192
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9199 =
                                                 let uu____9201 =
                                                   FStar_All.pipe_right
                                                     inst_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9201
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9208 =
                                                 FStar_Syntax_Print.term_to_string
                                                   lift3
                                                  in
                                               FStar_Util.format5
                                                 "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                 uu____9186 uu____9188
                                                 uu____9190 uu____9199
                                                 uu____9208
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____9184)
                                              in
                                           FStar_Errors.raise_error
                                             uu____9178 r)))
                                   in
                                match uu____9071 with
                                | (us2,lift3,lift_wp) ->
                                    let sub2 =
                                      let uu___990_9240 = sub1  in
                                      {
                                        FStar_Syntax_Syntax.source =
                                          (uu___990_9240.FStar_Syntax_Syntax.source);
                                        FStar_Syntax_Syntax.target =
                                          (uu___990_9240.FStar_Syntax_Syntax.target);
                                        FStar_Syntax_Syntax.lift_wp =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift_wp));
                                        FStar_Syntax_Syntax.lift =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift3))
                                      }  in
                                    ((let uu____9250 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env0)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____9250
                                      then
                                        let uu____9255 =
                                          FStar_Syntax_Print.sub_eff_to_string
                                            sub2
                                           in
                                        FStar_Util.print1
                                          "Final sub_effect: %s\n" uu____9255
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
          (let uu____9287 =
             let uu____9294 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9294
              in
           match uu____9287 with
           | (a,wp_a_src) ->
               let uu____9301 =
                 let uu____9308 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9308
                  in
               (match uu____9301 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9316 =
                        let uu____9319 =
                          let uu____9320 =
                            let uu____9327 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9327)  in
                          FStar_Syntax_Syntax.NT uu____9320  in
                        [uu____9319]  in
                      FStar_Syntax_Subst.subst uu____9316 wp_b_tgt  in
                    let expected_k =
                      let uu____9335 =
                        let uu____9344 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9351 =
                          let uu____9360 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9360]  in
                        uu____9344 :: uu____9351  in
                      let uu____9385 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9335 uu____9385  in
                    let repr_type eff_name a1 wp =
                      (let uu____9407 =
                         let uu____9409 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9409  in
                       if uu____9407
                       then
                         let uu____9412 =
                           let uu____9418 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9418)
                            in
                         let uu____9422 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9412 uu____9422
                       else ());
                      (let uu____9425 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9425 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ed.FStar_Syntax_Syntax.repr
                              in
                           let uu____9458 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9459 =
                             let uu____9466 =
                               let uu____9467 =
                                 let uu____9484 =
                                   let uu____9495 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9504 =
                                     let uu____9515 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9515]  in
                                   uu____9495 :: uu____9504  in
                                 (repr, uu____9484)  in
                               FStar_Syntax_Syntax.Tm_app uu____9467  in
                             FStar_Syntax_Syntax.mk uu____9466  in
                           uu____9459 FStar_Pervasives_Native.None uu____9458)
                       in
                    let uu____9560 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9733 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9744 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9744 with
                              | (usubst,uvs1) ->
                                  let uu____9767 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____9768 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____9767, uu____9768)
                            else (env, lift_wp)  in
                          (match uu____9733 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      tc_check_trivial_guard env1 lift_wp1
                                        expected_k
                                       in
                                    let uu____9818 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____9818))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____9889 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____9904 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____9904 with
                              | (usubst,uvs) ->
                                  let uu____9929 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____9929)
                            else ([], lift)  in
                          (match uu____9889 with
                           | (uvs,lift1) ->
                               ((let uu____9965 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____9965
                                 then
                                   let uu____9969 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____9969
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____9975 =
                                   let uu____9982 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____9982 lift1
                                    in
                                 match uu____9975 with
                                 | (lift2,comp,uu____10007) ->
                                     let uu____10008 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10008 with
                                      | (uu____10037,lift_wp,lift_elab) ->
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
                                            let uu____10069 =
                                              let uu____10080 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10080
                                               in
                                            let uu____10097 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10069, uu____10097)
                                          else
                                            (let uu____10126 =
                                               let uu____10137 =
                                                 let uu____10146 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10146)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10137
                                                in
                                             let uu____10161 =
                                               let uu____10170 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10170)  in
                                             (uu____10126, uu____10161))))))
                       in
                    (match uu____9560 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1070_10234 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1070_10234.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1070_10234.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1070_10234.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1070_10234.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1070_10234.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1070_10234.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1070_10234.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1070_10234.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1070_10234.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1070_10234.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1070_10234.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1070_10234.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1070_10234.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1070_10234.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1070_10234.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1070_10234.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1070_10234.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1070_10234.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1070_10234.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1070_10234.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1070_10234.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1070_10234.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1070_10234.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1070_10234.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1070_10234.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1070_10234.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1070_10234.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1070_10234.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1070_10234.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1070_10234.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1070_10234.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1070_10234.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1070_10234.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1070_10234.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1070_10234.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1070_10234.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1070_10234.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1070_10234.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1070_10234.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1070_10234.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1070_10234.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1070_10234.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1070_10234.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1070_10234.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10267 =
                                 let uu____10272 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10272 with
                                 | (usubst,uvs1) ->
                                     let uu____10295 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10296 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10295, uu____10296)
                                  in
                               (match uu____10267 with
                                | (env2,lift2) ->
                                    let uu____10301 =
                                      let uu____10308 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10308
                                       in
                                    (match uu____10301 with
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
                                             let uu____10334 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10335 =
                                               let uu____10342 =
                                                 let uu____10343 =
                                                   let uu____10360 =
                                                     let uu____10371 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10380 =
                                                       let uu____10391 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10391]  in
                                                     uu____10371 ::
                                                       uu____10380
                                                      in
                                                   (lift_wp1, uu____10360)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10343
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10342
                                                in
                                             uu____10335
                                               FStar_Pervasives_Native.None
                                               uu____10334
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10439 =
                                             let uu____10448 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10455 =
                                               let uu____10464 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10471 =
                                                 let uu____10480 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10480]  in
                                               uu____10464 :: uu____10471  in
                                             uu____10448 :: uu____10455  in
                                           let uu____10511 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10439 uu____10511
                                            in
                                         let uu____10514 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10514 with
                                          | (expected_k2,uu____10524,uu____10525)
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
                                                   let uu____10533 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10533))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10541 =
                             let uu____10543 =
                               let uu____10545 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10545
                                 FStar_List.length
                                in
                             uu____10543 <> Prims.int_one  in
                           if uu____10541
                           then
                             let uu____10568 =
                               let uu____10574 =
                                 let uu____10576 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10578 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10580 =
                                   let uu____10582 =
                                     let uu____10584 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10584
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10582
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10576 uu____10578 uu____10580
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10574)
                                in
                             FStar_Errors.raise_error uu____10568 r
                           else ());
                          (let uu____10611 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10614 =
                                  let uu____10616 =
                                    let uu____10619 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10619
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10616
                                    FStar_List.length
                                   in
                                uu____10614 <> Prims.int_one)
                              in
                           if uu____10611
                           then
                             let uu____10657 =
                               let uu____10663 =
                                 let uu____10665 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10667 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10669 =
                                   let uu____10671 =
                                     let uu____10673 =
                                       let uu____10676 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10676
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10673
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10671
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10665 uu____10667 uu____10669
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10663)
                                in
                             FStar_Errors.raise_error uu____10657 r
                           else ());
                          (let uu___1107_10718 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1107_10718.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1107_10718.FStar_Syntax_Syntax.target);
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
    fun uu____10749  ->
      fun r  ->
        match uu____10749 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____10772 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10800 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____10800 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____10831 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____10831 c  in
                     let uu____10840 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____10840, uvs1, tps1, c1))
               in
            (match uu____10772 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____10860 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____10860 with
                  | (tps2,c2) ->
                      let uu____10875 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____10875 with
                       | (tps3,env3,us) ->
                           let uu____10893 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____10893 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____10919)::uu____10920 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____10939 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____10947 =
                                    let uu____10949 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____10949  in
                                  if uu____10947
                                  then
                                    let uu____10952 =
                                      let uu____10958 =
                                        let uu____10960 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____10962 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____10960 uu____10962
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____10958)
                                       in
                                    FStar_Errors.raise_error uu____10952 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____10970 =
                                    let uu____10971 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____10971
                                     in
                                  match uu____10970 with
                                  | (uvs2,t) ->
                                      let uu____11000 =
                                        let uu____11005 =
                                          let uu____11018 =
                                            let uu____11019 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11019.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11018)  in
                                        match uu____11005 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11034,c5)) -> ([], c5)
                                        | (uu____11076,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11115 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11000 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11147 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11147 with
                                               | (uu____11152,t1) ->
                                                   let uu____11154 =
                                                     let uu____11160 =
                                                       let uu____11162 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11164 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11168 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11162
                                                         uu____11164
                                                         uu____11168
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11160)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11154 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  