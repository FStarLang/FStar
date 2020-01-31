open Prims
let (dmff_cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  = fun env  -> fun ed  -> FStar_TypeChecker_DMFF.cps_and_elaborate env ed 
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.string ->
        Prims.int ->
          (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) ->
            (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term *
              FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun eff_name  ->
      fun comb  ->
        fun n1  ->
          fun uu____58  ->
            match uu____58 with
            | (us,t) ->
                let uu____80 = FStar_Syntax_Subst.open_univ_vars us t  in
                (match uu____80 with
                 | (us1,t1) ->
                     let uu____93 =
                       let uu____98 =
                         let uu____105 =
                           FStar_TypeChecker_Env.push_univ_vars env us1  in
                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                           uu____105 t1
                          in
                       match uu____98 with
                       | (t2,lc,g) ->
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (t2, (lc.FStar_TypeChecker_Common.res_typ)))
                        in
                     (match uu____93 with
                      | (t2,ty) ->
                          let uu____122 =
                            FStar_TypeChecker_Util.generalize_universes env
                              t2
                             in
                          (match uu____122 with
                           | (g_us,t3) ->
                               let ty1 =
                                 FStar_Syntax_Subst.close_univ_vars g_us ty
                                  in
                               (if (FStar_List.length g_us) <> n1
                                then
                                  (let error =
                                     let uu____145 =
                                       FStar_Util.string_of_int n1  in
                                     let uu____147 =
                                       let uu____149 =
                                         FStar_All.pipe_right g_us
                                           FStar_List.length
                                          in
                                       FStar_All.pipe_right uu____149
                                         FStar_Util.string_of_int
                                        in
                                     let uu____156 =
                                       FStar_Syntax_Print.tscheme_to_string
                                         (g_us, t3)
                                        in
                                     FStar_Util.format5
                                       "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
                                       eff_name comb uu____145 uu____147
                                       uu____156
                                      in
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                       error) t3.FStar_Syntax_Syntax.pos;
                                   (match us1 with
                                    | [] -> ()
                                    | uu____165 ->
                                        let uu____166 =
                                          ((FStar_List.length us1) =
                                             (FStar_List.length g_us))
                                            &&
                                            (FStar_List.forall2
                                               (fun u1  ->
                                                  fun u2  ->
                                                    let uu____173 =
                                                      FStar_Syntax_Syntax.order_univ_name
                                                        u1 u2
                                                       in
                                                    uu____173 =
                                                      Prims.int_zero) us1
                                               g_us)
                                           in
                                        if uu____166
                                        then ()
                                        else
                                          (let uu____180 =
                                             let uu____186 =
                                               let uu____188 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   us1
                                                  in
                                               let uu____190 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   g_us
                                                  in
                                               FStar_Util.format4
                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                 eff_name comb uu____188
                                                 uu____190
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____186)
                                              in
                                           FStar_Errors.raise_error uu____180
                                             t3.FStar_Syntax_Syntax.pos)))
                                else ();
                                (g_us, t3, ty1)))))
  
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun quals  ->
        (let uu____217 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____217
         then
           let uu____222 = FStar_Syntax_Print.eff_decl_to_string false ed  in
           FStar_Util.print1 "Typechecking layered effect: \n\t%s\n"
             uu____222
         else ());
        if
          ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
            ||
            ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
               Prims.int_zero)
        then
          (let uu____240 =
             FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_UnexpectedEffect,
               (Prims.op_Hat
                  "Binders are not supported for layered effects ("
                  (Prims.op_Hat
                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str ")")))
             uu____240)
        else ();
        (let log_combinator s uu____269 =
           match uu____269 with
           | (us,t,ty) ->
               let uu____298 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____298
               then
                 let uu____303 = FStar_Syntax_Print.tscheme_to_string (us, t)
                    in
                 let uu____309 =
                   FStar_Syntax_Print.tscheme_to_string (us, ty)  in
                 FStar_Util.print4 "Typechecked %s:%s = %s:%s\n"
                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str s uu____303
                   uu____309
               else ()
            in
         let fresh_a_and_u_a a =
           let uu____334 = FStar_Syntax_Util.type_u ()  in
           FStar_All.pipe_right uu____334
             (fun uu____351  ->
                match uu____351 with
                | (t,u) ->
                    let uu____362 =
                      let uu____363 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t
                         in
                      FStar_All.pipe_right uu____363
                        FStar_Syntax_Syntax.mk_binder
                       in
                    (uu____362, u))
            in
         let fresh_x_a x a =
           let uu____377 =
             let uu____378 =
               let uu____379 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
               FStar_All.pipe_right uu____379 FStar_Syntax_Syntax.bv_to_name
                in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____378
              in
           FStar_All.pipe_right uu____377 FStar_Syntax_Syntax.mk_binder  in
         let check_and_gen1 =
           check_and_gen env0 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
            in
         let signature =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
              in
           let uu____431 =
             check_and_gen1 "signature" Prims.int_one
               ed.FStar_Syntax_Syntax.signature
              in
           match uu____431 with
           | (sig_us,sig_t,sig_ty) ->
               let uu____455 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                  in
               (match uu____455 with
                | (us,t) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____475 = fresh_a_and_u_a "a"  in
                    (match uu____475 with
                     | (a,u) ->
                         let rest_bs =
                           let uu____496 =
                             let uu____497 =
                               FStar_All.pipe_right a
                                 FStar_Pervasives_Native.fst
                                in
                             FStar_All.pipe_right uu____497
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           FStar_TypeChecker_Util.layered_effect_indices_as_binders
                             env r ed.FStar_Syntax_Syntax.mname
                             (sig_us, sig_t) u uu____496
                            in
                         let bs = a :: rest_bs  in
                         let k =
                           let uu____528 =
                             FStar_Syntax_Syntax.mk_Total
                               FStar_Syntax_Syntax.teff
                              in
                           FStar_Syntax_Util.arrow bs uu____528  in
                         let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                         (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                          (let uu____533 =
                             let uu____536 =
                               FStar_All.pipe_right k
                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                    env)
                                in
                             FStar_Syntax_Subst.close_univ_vars us uu____536
                              in
                           (sig_us, uu____533, sig_ty)))))
            in
         log_combinator "signature" signature;
         (let uu____545 =
            let repr_ts =
              let uu____567 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              FStar_All.pipe_right uu____567 FStar_Util.must  in
            let r =
              (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos
               in
            let uu____595 = check_and_gen1 "repr" Prims.int_one repr_ts  in
            match uu____595 with
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
                  let uu____626 =
                    let uu____627 = FStar_Syntax_Subst.compress repr_t1  in
                    uu____627.FStar_Syntax_Syntax.n  in
                  match uu____626 with
                  | FStar_Syntax_Syntax.Tm_abs (uu____630,t,uu____632) ->
                      let uu____657 =
                        let uu____658 = FStar_Syntax_Subst.compress t  in
                        uu____658.FStar_Syntax_Syntax.n  in
                      (match uu____657 with
                       | FStar_Syntax_Syntax.Tm_arrow (uu____661,c) ->
                           let uu____683 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____683
                             (FStar_TypeChecker_Env.norm_eff_name env0)
                       | uu____686 ->
                           let uu____687 =
                             let uu____693 =
                               let uu____695 =
                                 FStar_All.pipe_right
                                   ed.FStar_Syntax_Syntax.mname
                                   FStar_Ident.string_of_lid
                                  in
                               let uu____698 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.format2
                                 "repr body for %s is not an arrow (%s)"
                                 uu____695 uu____698
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu____693)
                              in
                           FStar_Errors.raise_error uu____687 r)
                  | uu____702 ->
                      let uu____703 =
                        let uu____709 =
                          let uu____711 =
                            FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                              FStar_Ident.string_of_lid
                             in
                          let uu____714 =
                            FStar_Syntax_Print.term_to_string repr_t1  in
                          FStar_Util.format2
                            "repr for %s is not an abstraction (%s)"
                            uu____711 uu____714
                           in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____709)  in
                      FStar_Errors.raise_error uu____703 r
                   in
                ((let uu____719 =
                    (FStar_All.pipe_right quals
                       (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                      &&
                      (let uu____725 =
                         FStar_TypeChecker_Env.is_total_effect env0
                           underlying_effect_lid
                          in
                       Prims.op_Negation uu____725)
                     in
                  if uu____719
                  then
                    let uu____728 =
                      let uu____734 =
                        let uu____736 =
                          FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                            FStar_Ident.string_of_lid
                           in
                        let uu____739 =
                          FStar_All.pipe_right underlying_effect_lid
                            FStar_Ident.string_of_lid
                           in
                        FStar_Util.format2
                          "Effect %s is marked total but its underlying effect %s is not total"
                          uu____736 uu____739
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____734)
                       in
                    FStar_Errors.raise_error uu____728 r
                  else ());
                 (let uu____746 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
                  match uu____746 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____770 = fresh_a_and_u_a "a"  in
                      (match uu____770 with
                       | (a,u) ->
                           let rest_bs =
                             let signature_ts =
                               let uu____796 = signature  in
                               match uu____796 with
                               | (us1,t,uu____811) -> (us1, t)  in
                             let uu____828 =
                               let uu____829 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____829
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               signature_ts u uu____828
                              in
                           let bs = a :: rest_bs  in
                           let k =
                             let uu____856 =
                               let uu____859 = FStar_Syntax_Util.type_u ()
                                  in
                               FStar_All.pipe_right uu____859
                                 (fun uu____872  ->
                                    match uu____872 with
                                    | (t,u1) ->
                                        let uu____879 =
                                          let uu____882 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____882
                                           in
                                        FStar_Syntax_Syntax.mk_Total' t
                                          uu____879)
                                in
                             FStar_Syntax_Util.arrow bs uu____856  in
                           let g = FStar_TypeChecker_Rel.teq env ty k  in
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (let uu____885 =
                               let uu____898 =
                                 let uu____901 =
                                   FStar_All.pipe_right k
                                     (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                        env)
                                    in
                                 FStar_Syntax_Subst.close_univ_vars us
                                   uu____901
                                  in
                               (repr_us, repr_t, uu____898)  in
                             (uu____885, underlying_effect_lid))))))
             in
          match uu____545 with
          | (repr,underlying_effect_lid) ->
              (log_combinator "repr" repr;
               (let fresh_repr r env u a_tm =
                  let signature_ts =
                    let uu____974 = signature  in
                    match uu____974 with | (us,t,uu____989) -> (us, t)  in
                  let repr_ts =
                    let uu____1007 = repr  in
                    match uu____1007 with | (us,t,uu____1022) -> (us, t)  in
                  FStar_TypeChecker_Util.fresh_effect_repr env r
                    ed.FStar_Syntax_Syntax.mname signature_ts
                    (FStar_Pervasives_Native.Some repr_ts) u a_tm
                   in
                let not_an_arrow_error comb n1 t r =
                  let uu____1072 =
                    let uu____1078 =
                      let uu____1080 = FStar_Util.string_of_int n1  in
                      let uu____1082 = FStar_Syntax_Print.tag_of_term t  in
                      let uu____1084 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.format5
                        "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                        (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str comb
                        uu____1080 uu____1082 uu____1084
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____1078)  in
                  FStar_Errors.raise_error uu____1072 r  in
                let return_repr =
                  let return_repr_ts =
                    let uu____1114 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_return_repr
                       in
                    FStar_All.pipe_right uu____1114 FStar_Util.must  in
                  let r =
                    (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos
                     in
                  let uu____1142 =
                    check_and_gen1 "return_repr" Prims.int_one return_repr_ts
                     in
                  match uu____1142 with
                  | (ret_us,ret_t,ret_ty) ->
                      let uu____1166 =
                        FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                      (match uu____1166 with
                       | (us,ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us  in
                           let uu____1186 = fresh_a_and_u_a "a"  in
                           (match uu____1186 with
                            | (a,u_a) ->
                                let x_a = fresh_x_a "x" a  in
                                let rest_bs =
                                  let uu____1217 =
                                    let uu____1218 =
                                      FStar_Syntax_Subst.compress ty  in
                                    uu____1218.FStar_Syntax_Syntax.n  in
                                  match uu____1217 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____1230) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (2))
                                      ->
                                      let uu____1258 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____1258 with
                                       | (a',uu____1268)::(x',uu____1270)::bs1
                                           ->
                                           let uu____1300 =
                                             let uu____1301 =
                                               let uu____1306 =
                                                 let uu____1309 =
                                                   let uu____1310 =
                                                     let uu____1317 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a', uu____1317)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____1310
                                                    in
                                                 [uu____1309]  in
                                               FStar_Syntax_Subst.subst_binders
                                                 uu____1306
                                                in
                                             FStar_All.pipe_right bs1
                                               uu____1301
                                              in
                                           let uu____1324 =
                                             let uu____1337 =
                                               let uu____1340 =
                                                 let uu____1341 =
                                                   let uu____1348 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       (FStar_Pervasives_Native.fst
                                                          x_a)
                                                      in
                                                   (x', uu____1348)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____1341
                                                  in
                                               [uu____1340]  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____1337
                                              in
                                           FStar_All.pipe_right uu____1300
                                             uu____1324)
                                  | uu____1363 ->
                                      not_an_arrow_error "return"
                                        (Prims.of_int (2)) ty r
                                   in
                                let bs = a :: x_a :: rest_bs  in
                                let uu____1387 =
                                  let uu____1392 =
                                    FStar_TypeChecker_Env.push_binders env bs
                                     in
                                  let uu____1393 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst a)
                                      FStar_Syntax_Syntax.bv_to_name
                                     in
                                  fresh_repr r uu____1392 u_a uu____1393  in
                                (match uu____1387 with
                                 | (repr1,g) ->
                                     let k =
                                       let uu____1413 =
                                         FStar_Syntax_Syntax.mk_Total' repr1
                                           (FStar_Pervasives_Native.Some u_a)
                                          in
                                       FStar_Syntax_Util.arrow bs uu____1413
                                        in
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env ty k  in
                                     ((let uu____1418 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           g_eq
                                          in
                                       FStar_TypeChecker_Rel.force_trivial_guard
                                         env uu____1418);
                                      (let uu____1419 =
                                         let uu____1422 =
                                           FStar_All.pipe_right k
                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                env)
                                            in
                                         FStar_Syntax_Subst.close_univ_vars
                                           us uu____1422
                                          in
                                       (ret_us, ret_t, uu____1419))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let bind_repr_ts =
                     let uu____1449 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_bind_repr
                        in
                     FStar_All.pipe_right uu____1449 FStar_Util.must  in
                   let r =
                     (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
                      in
                   let uu____1461 =
                     check_and_gen1 "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1461 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1485 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1485 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            let uu____1505 = fresh_a_and_u_a "a"  in
                            (match uu____1505 with
                             | (a,u_a) ->
                                 let uu____1525 = fresh_a_and_u_a "b"  in
                                 (match uu____1525 with
                                  | (b,u_b) ->
                                      let rest_bs =
                                        let uu____1554 =
                                          let uu____1555 =
                                            FStar_Syntax_Subst.compress ty
                                             in
                                          uu____1555.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1554 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs,uu____1567) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (4))
                                            ->
                                            let uu____1595 =
                                              FStar_Syntax_Subst.open_binders
                                                bs
                                               in
                                            (match uu____1595 with
                                             | (a',uu____1605)::(b',uu____1607)::bs1
                                                 ->
                                                 let uu____1637 =
                                                   let uu____1638 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             -
                                                             (Prims.of_int (2))))
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____1638
                                                     FStar_Pervasives_Native.fst
                                                    in
                                                 let uu____1736 =
                                                   let uu____1749 =
                                                     let uu____1752 =
                                                       let uu____1753 =
                                                         let uu____1760 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                a)
                                                            in
                                                         (a', uu____1760)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____1753
                                                        in
                                                     let uu____1767 =
                                                       let uu____1770 =
                                                         let uu____1771 =
                                                           let uu____1778 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               (FStar_Pervasives_Native.fst
                                                                  b)
                                                              in
                                                           (b', uu____1778)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____1771
                                                          in
                                                       [uu____1770]  in
                                                     uu____1752 :: uu____1767
                                                      in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____1749
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____1637 uu____1736)
                                        | uu____1793 ->
                                            not_an_arrow_error "bind"
                                              (Prims.of_int (4)) ty r
                                         in
                                      let bs = a :: b :: rest_bs  in
                                      let uu____1817 =
                                        let uu____1828 =
                                          let uu____1833 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____1834 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____1833 u_a
                                            uu____1834
                                           in
                                        match uu____1828 with
                                        | (repr1,g) ->
                                            let uu____1849 =
                                              let uu____1856 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1
                                                 in
                                              FStar_All.pipe_right uu____1856
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            (uu____1849, g)
                                         in
                                      (match uu____1817 with
                                       | (f,guard_f) ->
                                           let uu____1896 =
                                             let x_a = fresh_x_a "x" a  in
                                             let uu____1909 =
                                               let uu____1914 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env
                                                   (FStar_List.append bs
                                                      [x_a])
                                                  in
                                               let uu____1933 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.fst
                                                      b)
                                                   FStar_Syntax_Syntax.bv_to_name
                                                  in
                                               fresh_repr r uu____1914 u_b
                                                 uu____1933
                                                in
                                             match uu____1909 with
                                             | (repr1,g) ->
                                                 let uu____1948 =
                                                   let uu____1955 =
                                                     let uu____1956 =
                                                       let uu____1957 =
                                                         let uu____1960 =
                                                           let uu____1963 =
                                                             FStar_TypeChecker_Env.new_u_univ
                                                               ()
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1963
                                                            in
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1 uu____1960
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         [x_a] uu____1957
                                                        in
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "g"
                                                       FStar_Pervasives_Native.None
                                                       uu____1956
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____1955
                                                     FStar_Syntax_Syntax.mk_binder
                                                    in
                                                 (uu____1948, g)
                                              in
                                           (match uu____1896 with
                                            | (g,guard_g) ->
                                                let uu____2015 =
                                                  let uu____2020 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____2021 =
                                                    FStar_All.pipe_right
                                                      (FStar_Pervasives_Native.fst
                                                         b)
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____2020 u_b
                                                    uu____2021
                                                   in
                                                (match uu____2015 with
                                                 | (repr1,guard_repr) ->
                                                     let k =
                                                       let uu____2041 =
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1
                                                           (FStar_Pervasives_Native.Some
                                                              u_b)
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         (FStar_List.append
                                                            bs [f; g])
                                                         uu____2041
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
                                                      (let uu____2070 =
                                                         let uu____2073 =
                                                           FStar_All.pipe_right
                                                             k
                                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                env)
                                                            in
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           bind_us uu____2073
                                                          in
                                                       (bind_us, bind_t,
                                                         uu____2070)))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2100 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2100 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2128 =
                      check_and_gen1 "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2128 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2153 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2153
                          then
                            let uu____2158 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2164 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2158 uu____2164
                          else ());
                         (let uu____2173 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2173 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              let uu____2193 = fresh_a_and_u_a "a"  in
                              (match uu____2193 with
                               | (a,u) ->
                                   let rest_bs =
                                     let uu____2222 =
                                       let uu____2223 =
                                         FStar_Syntax_Subst.compress ty  in
                                       uu____2223.FStar_Syntax_Syntax.n  in
                                     match uu____2222 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (bs,uu____2235) when
                                         (FStar_List.length bs) >=
                                           (Prims.of_int (2))
                                         ->
                                         let uu____2263 =
                                           FStar_Syntax_Subst.open_binders bs
                                            in
                                         (match uu____2263 with
                                          | (a',uu____2273)::bs1 ->
                                              let uu____2293 =
                                                let uu____2294 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.splitAt
                                                       ((FStar_List.length
                                                           bs1)
                                                          - Prims.int_one))
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2294
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              let uu____2392 =
                                                let uu____2405 =
                                                  let uu____2408 =
                                                    let uu____2409 =
                                                      let uu____2416 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____2416)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____2409
                                                     in
                                                  [uu____2408]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____2405
                                                 in
                                              FStar_All.pipe_right uu____2293
                                                uu____2392)
                                     | uu____2431 ->
                                         not_an_arrow_error "stronger"
                                           (Prims.of_int (2)) ty r
                                      in
                                   let bs = a :: rest_bs  in
                                   let uu____2449 =
                                     let uu____2460 =
                                       let uu____2465 =
                                         FStar_TypeChecker_Env.push_binders
                                           env bs
                                          in
                                       let uu____2466 =
                                         FStar_All.pipe_right
                                           (FStar_Pervasives_Native.fst a)
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       fresh_repr r uu____2465 u uu____2466
                                        in
                                     match uu____2460 with
                                     | (repr1,g) ->
                                         let uu____2481 =
                                           let uu____2488 =
                                             FStar_Syntax_Syntax.gen_bv "f"
                                               FStar_Pervasives_Native.None
                                               repr1
                                              in
                                           FStar_All.pipe_right uu____2488
                                             FStar_Syntax_Syntax.mk_binder
                                            in
                                         (uu____2481, g)
                                      in
                                   (match uu____2449 with
                                    | (f,guard_f) ->
                                        let uu____2528 =
                                          let uu____2533 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____2534 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____2533 u
                                            uu____2534
                                           in
                                        (match uu____2528 with
                                         | (ret_t,guard_ret_t) ->
                                             let pure_wp_t =
                                               let pure_wp_ts =
                                                 let uu____2553 =
                                                   FStar_TypeChecker_Env.lookup_definition
                                                     [FStar_TypeChecker_Env.NoDelta]
                                                     env
                                                     FStar_Parser_Const.pure_wp_lid
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2553 FStar_Util.must
                                                  in
                                               let uu____2570 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   pure_wp_ts
                                                  in
                                               match uu____2570 with
                                               | (uu____2575,pure_wp_t) ->
                                                   let uu____2577 =
                                                     let uu____2582 =
                                                       let uu____2583 =
                                                         FStar_All.pipe_right
                                                           ret_t
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____2583]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       pure_wp_t uu____2582
                                                      in
                                                   uu____2577
                                                     FStar_Pervasives_Native.None
                                                     r
                                                in
                                             let uu____2616 =
                                               let reason =
                                                 FStar_Util.format1
                                                   "implicit for pure_wp in checking stronger for %s"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                  in
                                               let uu____2632 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs
                                                  in
                                               FStar_TypeChecker_Util.new_implicit_var
                                                 reason r uu____2632
                                                 pure_wp_t
                                                in
                                             (match uu____2616 with
                                              | (pure_wp_uvar,uu____2646,guard_wp)
                                                  ->
                                                  let c =
                                                    let uu____2661 =
                                                      let uu____2662 =
                                                        let uu____2663 =
                                                          FStar_TypeChecker_Env.new_u_univ
                                                            ()
                                                           in
                                                        [uu____2663]  in
                                                      let uu____2664 =
                                                        let uu____2675 =
                                                          FStar_All.pipe_right
                                                            pure_wp_uvar
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____2675]  in
                                                      {
                                                        FStar_Syntax_Syntax.comp_univs
                                                          = uu____2662;
                                                        FStar_Syntax_Syntax.effect_name
                                                          =
                                                          FStar_Parser_Const.effect_PURE_lid;
                                                        FStar_Syntax_Syntax.result_typ
                                                          = ret_t;
                                                        FStar_Syntax_Syntax.effect_args
                                                          = uu____2664;
                                                        FStar_Syntax_Syntax.flags
                                                          = []
                                                      }  in
                                                    FStar_Syntax_Syntax.mk_Comp
                                                      uu____2661
                                                     in
                                                  let k =
                                                    FStar_Syntax_Util.arrow
                                                      (FStar_List.append bs
                                                         [f]) c
                                                     in
                                                  ((let uu____2730 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "LayeredEffects")
                                                       in
                                                    if uu____2730
                                                    then
                                                      let uu____2735 =
                                                        FStar_Syntax_Print.term_to_string
                                                          k
                                                         in
                                                      FStar_Util.print1
                                                        "Expected type before unification: %s\n"
                                                        uu____2735
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
                                                     let uu____2743 =
                                                       let uu____2746 =
                                                         FStar_All.pipe_right
                                                           k1
                                                           (FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Env.Beta;
                                                              FStar_TypeChecker_Env.Eager_unfolding]
                                                              env)
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____2746
                                                         (FStar_Syntax_Subst.close_univ_vars
                                                            stronger_us)
                                                        in
                                                     (stronger_us,
                                                       stronger_t,
                                                       uu____2743))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2775 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2775 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2803 =
                       check_and_gen1 "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2803 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2827 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2827 with
                          | (us,t) ->
                              let uu____2846 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2846 with
                               | (uu____2863,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   let uu____2866 = fresh_a_and_u_a "a"  in
                                   (match uu____2866 with
                                    | (a,u_a) ->
                                        let rest_bs =
                                          let uu____2895 =
                                            let uu____2896 =
                                              FStar_Syntax_Subst.compress ty
                                               in
                                            uu____2896.FStar_Syntax_Syntax.n
                                             in
                                          match uu____2895 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,uu____2908) when
                                              (FStar_List.length bs) >=
                                                (Prims.of_int (4))
                                              ->
                                              let uu____2936 =
                                                FStar_Syntax_Subst.open_binders
                                                  bs
                                                 in
                                              (match uu____2936 with
                                               | (a',uu____2946)::bs1 ->
                                                   let uu____2966 =
                                                     let uu____2967 =
                                                       FStar_All.pipe_right
                                                         bs1
                                                         (FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs1)
                                                               -
                                                               (Prims.of_int (3))))
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____2967
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____3065 =
                                                     let uu____3078 =
                                                       let uu____3081 =
                                                         let uu____3082 =
                                                           let uu____3089 =
                                                             let uu____3092 =
                                                               FStar_All.pipe_right
                                                                 a
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____3092
                                                               FStar_Syntax_Syntax.bv_to_name
                                                              in
                                                           (a', uu____3089)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____3082
                                                          in
                                                       [uu____3081]  in
                                                     FStar_Syntax_Subst.subst_binders
                                                       uu____3078
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____2966 uu____3065)
                                          | uu____3113 ->
                                              not_an_arrow_error
                                                "if_then_else"
                                                (Prims.of_int (4)) ty r
                                           in
                                        let bs = a :: rest_bs  in
                                        let uu____3131 =
                                          let uu____3142 =
                                            let uu____3147 =
                                              FStar_TypeChecker_Env.push_binders
                                                env bs
                                               in
                                            let uu____3148 =
                                              let uu____3149 =
                                                FStar_All.pipe_right a
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right uu____3149
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            fresh_repr r uu____3147 u_a
                                              uu____3148
                                             in
                                          match uu____3142 with
                                          | (repr1,g) ->
                                              let uu____3170 =
                                                let uu____3177 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "f"
                                                    FStar_Pervasives_Native.None
                                                    repr1
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3177
                                                  FStar_Syntax_Syntax.mk_binder
                                                 in
                                              (uu____3170, g)
                                           in
                                        (match uu____3131 with
                                         | (f_bs,guard_f) ->
                                             let uu____3217 =
                                               let uu____3228 =
                                                 let uu____3233 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env bs
                                                    in
                                                 let uu____3234 =
                                                   let uu____3235 =
                                                     FStar_All.pipe_right a
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3235
                                                     FStar_Syntax_Syntax.bv_to_name
                                                    in
                                                 fresh_repr r uu____3233 u_a
                                                   uu____3234
                                                  in
                                               match uu____3228 with
                                               | (repr1,g) ->
                                                   let uu____3256 =
                                                     let uu____3263 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "g"
                                                         FStar_Pervasives_Native.None
                                                         repr1
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3263
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   (uu____3256, g)
                                                in
                                             (match uu____3217 with
                                              | (g_bs,guard_g) ->
                                                  let p_b =
                                                    let uu____3310 =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "p"
                                                        FStar_Pervasives_Native.None
                                                        FStar_Syntax_Util.ktype0
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3310
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  let uu____3318 =
                                                    let uu____3323 =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env
                                                        (FStar_List.append bs
                                                           [p_b])
                                                       in
                                                    let uu____3342 =
                                                      let uu____3343 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3343
                                                        FStar_Syntax_Syntax.bv_to_name
                                                       in
                                                    fresh_repr r uu____3323
                                                      u_a uu____3342
                                                     in
                                                  (match uu____3318 with
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
                                                        (let uu____3403 =
                                                           let uu____3406 =
                                                             FStar_All.pipe_right
                                                               k
                                                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                  env)
                                                              in
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             if_then_else_us
                                                             uu____3406
                                                            in
                                                         (if_then_else_us,
                                                           uu____3403,
                                                           if_then_else_ty)))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3417 =
                        let uu____3420 =
                          let uu____3429 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3429 FStar_Util.must  in
                        FStar_All.pipe_right uu____3420
                          FStar_Pervasives_Native.snd
                         in
                      uu____3417.FStar_Syntax_Syntax.pos  in
                    let uu____3458 = if_then_else1  in
                    match uu____3458 with
                    | (ite_us,ite_t,uu____3473) ->
                        let uu____3486 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3486 with
                         | (us,ite_t1) ->
                             let uu____3493 =
                               let uu____3504 =
                                 let uu____3505 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3505.FStar_Syntax_Syntax.n  in
                               match uu____3504 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3519,uu____3520) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3546 =
                                     let uu____3553 =
                                       let uu____3556 =
                                         let uu____3559 =
                                           let uu____3568 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3568
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3559
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3556
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3553
                                       (fun l  ->
                                          let uu____3712 = l  in
                                          match uu____3712 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3546 with
                                    | (f,g,p) ->
                                        let uu____3737 =
                                          let uu____3738 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3738 bs1
                                           in
                                        let uu____3739 =
                                          let uu____3740 =
                                            let uu____3745 =
                                              let uu____3746 =
                                                let uu____3749 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3749
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____3746
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____3745
                                             in
                                          uu____3740
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____3737, uu____3739, f, g, p))
                               | uu____3776 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3493 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____3793 =
                                    let uu____3802 = stronger_repr  in
                                    match uu____3802 with
                                    | (uu____3823,subcomp_t,subcomp_ty) ->
                                        let uu____3838 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3838 with
                                         | (uu____3851,subcomp_t1) ->
                                             let bs_except_last =
                                               let uu____3862 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____3862 with
                                               | (uu____3875,subcomp_ty1) ->
                                                   let uu____3877 =
                                                     let uu____3878 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____3878.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____3877 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____3890) ->
                                                        let uu____3911 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3911
                                                          FStar_Pervasives_Native.fst
                                                    | uu____4017 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             let aux t =
                                               let uu____4035 =
                                                 let uu____4040 =
                                                   let uu____4041 =
                                                     let uu____4044 =
                                                       FStar_All.pipe_right
                                                         bs_except_last
                                                         (FStar_List.map
                                                            (fun uu____4064 
                                                               ->
                                                               FStar_Syntax_Syntax.tun))
                                                        in
                                                     FStar_List.append
                                                       uu____4044 [t]
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____4041
                                                     (FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg)
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   subcomp_t1 uu____4040
                                                  in
                                               uu____4035
                                                 FStar_Pervasives_Native.None
                                                 r
                                                in
                                             let uu____4073 = aux f_t  in
                                             let uu____4076 = aux g_t  in
                                             (uu____4073, uu____4076))
                                     in
                                  (match uu____3793 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4093 =
                                         let aux t =
                                           let uu____4110 =
                                             let uu____4117 =
                                               let uu____4118 =
                                                 let uu____4145 =
                                                   let uu____4162 =
                                                     let uu____4171 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4171
                                                      in
                                                   (uu____4162,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4145,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4118
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4117
                                              in
                                           uu____4110
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4212 = aux subcomp_f  in
                                         let uu____4213 = aux subcomp_g  in
                                         (uu____4212, uu____4213)  in
                                       (match uu____4093 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4217 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4217
                                              then
                                                let uu____4222 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4224 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4222 uu____4224
                                              else ());
                                             (let uu____4229 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4229 with
                                              | (uu____4236,uu____4237,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4240 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4240 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4242 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4242 with
                                                    | (uu____4249,uu____4250,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4256 =
                                                              let uu____4261
                                                                =
                                                                let uu____4262
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4262
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4263
                                                                =
                                                                let uu____4264
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4264]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4261
                                                                uu____4263
                                                               in
                                                            uu____4256
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4297 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4297 g_g
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
                        (let uu____4321 =
                           let uu____4327 =
                             let uu____4329 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4329
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4327)
                            in
                         FStar_Errors.raise_error uu____4321 r)
                      else ();
                      (let uu____4336 =
                         let uu____4341 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4341 with
                         | (usubst,us) ->
                             let uu____4364 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4365 =
                               let uu___420_4366 = act  in
                               let uu____4367 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4368 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___420_4366.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___420_4366.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___420_4366.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4367;
                                 FStar_Syntax_Syntax.action_typ = uu____4368
                               }  in
                             (uu____4364, uu____4365)
                          in
                       match uu____4336 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4372 =
                               let uu____4373 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4373.FStar_Syntax_Syntax.n  in
                             match uu____4372 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4399 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4399
                                 then
                                   let repr_ts =
                                     let uu____4403 = repr  in
                                     match uu____4403 with
                                     | (us,t,uu____4418) -> (us, t)  in
                                   let repr1 =
                                     let uu____4436 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4436
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4448 =
                                       let uu____4453 =
                                         let uu____4454 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4454 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4453
                                        in
                                     uu____4448 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4472 =
                                       let uu____4475 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4475
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4472
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4478 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4479 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4479 with
                            | (act_typ1,uu____4487,g_t) ->
                                let uu____4489 =
                                  let uu____4496 =
                                    let uu___445_4497 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___445_4497.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___445_4497.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___445_4497.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___445_4497.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___445_4497.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___445_4497.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___445_4497.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___445_4497.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___445_4497.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___445_4497.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___445_4497.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___445_4497.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___445_4497.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___445_4497.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___445_4497.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___445_4497.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___445_4497.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___445_4497.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___445_4497.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___445_4497.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___445_4497.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___445_4497.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___445_4497.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___445_4497.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___445_4497.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___445_4497.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___445_4497.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___445_4497.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___445_4497.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___445_4497.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___445_4497.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___445_4497.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___445_4497.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___445_4497.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___445_4497.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___445_4497.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___445_4497.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___445_4497.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___445_4497.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___445_4497.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___445_4497.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___445_4497.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___445_4497.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___445_4497.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4496
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4489 with
                                 | (act_defn,uu____4500,g_d) ->
                                     ((let uu____4503 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4503
                                       then
                                         let uu____4508 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4510 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4508 uu____4510
                                       else ());
                                      (let uu____4515 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4523 =
                                           let uu____4524 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4524.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4523 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4534) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4557 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4557 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4573 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4573 with
                                                   | (a_tm,uu____4593,g_tm)
                                                       ->
                                                       let uu____4607 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4607 with
                                                        | (repr1,g) ->
                                                            let uu____4620 =
                                                              let uu____4623
                                                                =
                                                                let uu____4626
                                                                  =
                                                                  let uu____4629
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4629
                                                                    (
                                                                    fun _4632
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4632)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4626
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4623
                                                               in
                                                            let uu____4633 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4620,
                                                              uu____4633))))
                                         | uu____4636 ->
                                             let uu____4637 =
                                               let uu____4643 =
                                                 let uu____4645 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____4645
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4643)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4637 r
                                          in
                                       match uu____4515 with
                                       | (k,g_k) ->
                                           ((let uu____4662 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4662
                                             then
                                               let uu____4667 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4667
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4675 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4675
                                              then
                                                let uu____4680 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4680
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4693 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____4693
                                                   in
                                                let repr_args t =
                                                  let uu____4714 =
                                                    let uu____4715 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4715.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4714 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4767 =
                                                        let uu____4768 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4768.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4767 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4777,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4787 ->
                                                           let uu____4788 =
                                                             let uu____4794 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4794)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4788 r)
                                                  | uu____4803 ->
                                                      let uu____4804 =
                                                        let uu____4810 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4810)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4804 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4820 =
                                                  let uu____4821 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4821.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4820 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4846 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4846 with
                                                     | (bs1,c1) ->
                                                         let uu____4853 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____4853
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
                                                              let uu____4864
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4864))
                                                | uu____4867 ->
                                                    let uu____4868 =
                                                      let uu____4874 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____4874)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____4868 r
                                                 in
                                              (let uu____4878 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____4878
                                               then
                                                 let uu____4883 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____4883
                                               else ());
                                              (let act2 =
                                                 let uu____4889 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____4889 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___518_4903 =
                                                         act1  in
                                                       let uu____4904 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___518_4903.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___518_4903.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___518_4903.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____4904
                                                       }
                                                     else
                                                       (let uu____4907 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____4914
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____4914
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____4907
                                                        then
                                                          let uu___523_4919 =
                                                            act1  in
                                                          let uu____4920 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___523_4919.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___523_4919.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___523_4919.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___523_4919.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____4920
                                                          }
                                                        else
                                                          (let uu____4923 =
                                                             let uu____4929 =
                                                               let uu____4931
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____4933
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____4931
                                                                 uu____4933
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____4929)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4923 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____4958 =
                      match uu____4958 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5003 =
                        let uu____5004 = tschemes_of repr  in
                        let uu____5009 = tschemes_of return_repr  in
                        let uu____5014 = tschemes_of bind_repr  in
                        let uu____5019 = tschemes_of stronger_repr  in
                        let uu____5024 = tschemes_of if_then_else1  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5004;
                          FStar_Syntax_Syntax.l_return = uu____5009;
                          FStar_Syntax_Syntax.l_bind = uu____5014;
                          FStar_Syntax_Syntax.l_subcomp = uu____5019;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5024
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5003  in
                    let uu___532_5029 = ed  in
                    let uu____5030 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___532_5029.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___532_5029.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___532_5029.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___532_5029.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5037 = signature  in
                         match uu____5037 with | (us,t,uu____5052) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5030;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___532_5029.FStar_Syntax_Syntax.eff_attrs)
                    }))))))))
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____5090 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5090
         then
           let uu____5095 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5095
         else ());
        (let uu____5101 =
           let uu____5106 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5106 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5130 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5130  in
               let uu____5131 =
                 let uu____5138 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5138 bs  in
               (match uu____5131 with
                | (bs1,uu____5144,uu____5145) ->
                    let uu____5146 =
                      let tmp_t =
                        let uu____5156 =
                          let uu____5159 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5164  ->
                                 FStar_Pervasives_Native.Some _5164)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5159
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5156  in
                      let uu____5165 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5165 with
                      | (us,tmp_t1) ->
                          let uu____5182 =
                            let uu____5183 =
                              let uu____5184 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5184
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5183
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5182)
                       in
                    (match uu____5146 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5221 ->
                              let uu____5224 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5231 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5231 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5224
                              then (us, bs2)
                              else
                                (let uu____5242 =
                                   let uu____5248 =
                                     let uu____5250 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5252 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5250 uu____5252
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5248)
                                    in
                                 let uu____5256 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5242
                                   uu____5256))))
            in
         match uu____5101 with
         | (us,bs) ->
             let ed1 =
               let uu___566_5264 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___566_5264.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___566_5264.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___566_5264.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___566_5264.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___566_5264.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___566_5264.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5265 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5265 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5284 =
                    let uu____5289 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5289  in
                  (match uu____5284 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5310 =
                           match uu____5310 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5330 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5330 t  in
                               let uu____5339 =
                                 let uu____5340 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5340 t1  in
                               (us1, uu____5339)
                            in
                         let uu___580_5345 = ed1  in
                         let uu____5346 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5347 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5348 =
                           FStar_List.map
                             (fun a  ->
                                let uu___583_5356 = a  in
                                let uu____5357 =
                                  let uu____5358 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5358  in
                                let uu____5369 =
                                  let uu____5370 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5370  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___583_5356.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___583_5356.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___583_5356.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___583_5356.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5357;
                                  FStar_Syntax_Syntax.action_typ = uu____5369
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___580_5345.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___580_5345.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___580_5345.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___580_5345.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5346;
                           FStar_Syntax_Syntax.combinators = uu____5347;
                           FStar_Syntax_Syntax.actions = uu____5348;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___580_5345.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5382 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5382
                         then
                           let uu____5387 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5387
                         else ());
                        (let env =
                           let uu____5394 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5394
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5429 k =
                           match uu____5429 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5449 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5449 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5458 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5458 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5459 =
                                            let uu____5466 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5466 t1
                                             in
                                          (match uu____5459 with
                                           | (t2,uu____5468,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5471 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5471 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5487 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5489 =
                                                 let uu____5491 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5491
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5487 uu____5489
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5506 ->
                                               let uu____5507 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5514 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5514 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5507
                                               then (g_us, t3)
                                               else
                                                 (let uu____5525 =
                                                    let uu____5531 =
                                                      let uu____5533 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5535 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5533
                                                        uu____5535
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5531)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5525
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5543 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5543
                          then
                            let uu____5548 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5548
                          else ());
                         (let fresh_a_and_wp uu____5564 =
                            let fail1 t =
                              let uu____5577 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5577
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5593 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5593 with
                            | (uu____5604,signature1) ->
                                let uu____5606 =
                                  let uu____5607 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5607.FStar_Syntax_Syntax.n  in
                                (match uu____5606 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5617) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5646)::(wp,uu____5648)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5677 -> fail1 signature1)
                                 | uu____5678 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5692 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5692
                            then
                              let uu____5697 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____5697
                            else ()  in
                          let ret_wp =
                            let uu____5703 = fresh_a_and_wp ()  in
                            match uu____5703 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5719 =
                                    let uu____5728 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5735 =
                                      let uu____5744 =
                                        let uu____5751 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5751
                                         in
                                      [uu____5744]  in
                                    uu____5728 :: uu____5735  in
                                  let uu____5770 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5719
                                    uu____5770
                                   in
                                let uu____5773 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____5773
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5787 = fresh_a_and_wp ()  in
                             match uu____5787 with
                             | (a,wp_sort_a) ->
                                 let uu____5800 = fresh_a_and_wp ()  in
                                 (match uu____5800 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5816 =
                                          let uu____5825 =
                                            let uu____5832 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5832
                                             in
                                          [uu____5825]  in
                                        let uu____5845 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5816
                                          uu____5845
                                         in
                                      let k =
                                        let uu____5851 =
                                          let uu____5860 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5867 =
                                            let uu____5876 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5883 =
                                              let uu____5892 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____5899 =
                                                let uu____5908 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____5915 =
                                                  let uu____5924 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____5924]  in
                                                uu____5908 :: uu____5915  in
                                              uu____5892 :: uu____5899  in
                                            uu____5876 :: uu____5883  in
                                          uu____5860 :: uu____5867  in
                                        let uu____5967 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5851
                                          uu____5967
                                         in
                                      let uu____5970 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____5970
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____5984 = fresh_a_and_wp ()  in
                              match uu____5984 with
                              | (a,wp_sort_a) ->
                                  let uu____5997 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____5997 with
                                   | (t,uu____6003) ->
                                       let k =
                                         let uu____6007 =
                                           let uu____6016 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6023 =
                                             let uu____6032 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6039 =
                                               let uu____6048 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6048]  in
                                             uu____6032 :: uu____6039  in
                                           uu____6016 :: uu____6023  in
                                         let uu____6079 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6007
                                           uu____6079
                                          in
                                       let uu____6082 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6082
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else1 =
                               let uu____6096 = fresh_a_and_wp ()  in
                               match uu____6096 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6110 =
                                       let uu____6113 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6113
                                        in
                                     let uu____6114 =
                                       let uu____6115 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6115
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6110
                                       uu____6114
                                      in
                                   let k =
                                     let uu____6127 =
                                       let uu____6136 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6143 =
                                         let uu____6152 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6159 =
                                           let uu____6168 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6175 =
                                             let uu____6184 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6184]  in
                                           uu____6168 :: uu____6175  in
                                         uu____6152 :: uu____6159  in
                                       uu____6136 :: uu____6143  in
                                     let uu____6221 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6127
                                       uu____6221
                                      in
                                   let uu____6224 =
                                     let uu____6229 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6229
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6224
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else1;
                             (let ite_wp =
                                let uu____6261 = fresh_a_and_wp ()  in
                                match uu____6261 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6277 =
                                        let uu____6286 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6293 =
                                          let uu____6302 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6302]  in
                                        uu____6286 :: uu____6293  in
                                      let uu____6327 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6277
                                        uu____6327
                                       in
                                    let uu____6330 =
                                      let uu____6335 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6335
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6330
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6351 = fresh_a_and_wp ()  in
                                 match uu____6351 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6365 =
                                         let uu____6368 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6368
                                          in
                                       let uu____6369 =
                                         let uu____6370 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6370
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6365
                                         uu____6369
                                        in
                                     let wp_sort_b_a =
                                       let uu____6382 =
                                         let uu____6391 =
                                           let uu____6398 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6398
                                            in
                                         [uu____6391]  in
                                       let uu____6411 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6382
                                         uu____6411
                                        in
                                     let k =
                                       let uu____6417 =
                                         let uu____6426 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6433 =
                                           let uu____6442 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6449 =
                                             let uu____6458 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6458]  in
                                           uu____6442 :: uu____6449  in
                                         uu____6426 :: uu____6433  in
                                       let uu____6489 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6417
                                         uu____6489
                                        in
                                     let uu____6492 =
                                       let uu____6497 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6497
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6492
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6513 = fresh_a_and_wp ()  in
                                  match uu____6513 with
                                  | (a,wp_sort_a) ->
                                      let uu____6526 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6526 with
                                       | (t,uu____6532) ->
                                           let k =
                                             let uu____6536 =
                                               let uu____6545 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6552 =
                                                 let uu____6561 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6561]  in
                                               uu____6545 :: uu____6552  in
                                             let uu____6586 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6536 uu____6586
                                              in
                                           let trivial =
                                             let uu____6590 =
                                               let uu____6595 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6595 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6590
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____6610 =
                                  let uu____6627 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____6627 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6656 ->
                                      let repr =
                                        let uu____6660 = fresh_a_and_wp ()
                                           in
                                        match uu____6660 with
                                        | (a,wp_sort_a) ->
                                            let uu____6673 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____6673 with
                                             | (t,uu____6679) ->
                                                 let k =
                                                   let uu____6683 =
                                                     let uu____6692 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6699 =
                                                       let uu____6708 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____6708]  in
                                                     uu____6692 :: uu____6699
                                                      in
                                                   let uu____6733 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6683 uu____6733
                                                    in
                                                 let uu____6736 =
                                                   let uu____6741 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6741
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____6736
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____6785 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____6785 with
                                          | (uu____6792,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____6795 =
                                                let uu____6802 =
                                                  let uu____6803 =
                                                    let uu____6820 =
                                                      let uu____6831 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____6848 =
                                                        let uu____6859 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____6859]  in
                                                      uu____6831 ::
                                                        uu____6848
                                                       in
                                                    (repr2, uu____6820)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6803
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____6802
                                                 in
                                              uu____6795
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____6925 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____6925 wp  in
                                        let destruct_repr t =
                                          let uu____6940 =
                                            let uu____6941 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____6941.FStar_Syntax_Syntax.n
                                             in
                                          match uu____6940 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____6952,(t1,uu____6954)::
                                               (wp,uu____6956)::[])
                                              -> (t1, wp)
                                          | uu____7015 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7031 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7031
                                              FStar_Util.must
                                             in
                                          let uu____7058 = fresh_a_and_wp ()
                                             in
                                          match uu____7058 with
                                          | (a,uu____7066) ->
                                              let x_a =
                                                let uu____7072 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7072
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7080 =
                                                    let uu____7085 =
                                                      let uu____7086 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7086
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____7095 =
                                                      let uu____7096 =
                                                        let uu____7105 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7105
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7114 =
                                                        let uu____7125 =
                                                          let uu____7134 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7134
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7125]  in
                                                      uu____7096 ::
                                                        uu____7114
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____7085 uu____7095
                                                     in
                                                  uu____7080
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7170 =
                                                  let uu____7179 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7186 =
                                                    let uu____7195 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7195]  in
                                                  uu____7179 :: uu____7186
                                                   in
                                                let uu____7220 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7170 uu____7220
                                                 in
                                              let uu____7223 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7223 with
                                               | (k1,uu____7231,uu____7232)
                                                   ->
                                                   let env1 =
                                                     let uu____7236 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7236
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
                                             let uu____7249 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7249
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7287 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7287
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7288 = fresh_a_and_wp ()
                                              in
                                           match uu____7288 with
                                           | (a,wp_sort_a) ->
                                               let uu____7301 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7301 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7317 =
                                                        let uu____7326 =
                                                          let uu____7333 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7333
                                                           in
                                                        [uu____7326]  in
                                                      let uu____7346 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7317 uu____7346
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
                                                      let uu____7354 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7354
                                                       in
                                                    let wp_g_x =
                                                      let uu____7359 =
                                                        let uu____7364 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g
                                                           in
                                                        let uu____7365 =
                                                          let uu____7366 =
                                                            let uu____7375 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7375
                                                              FStar_Syntax_Syntax.as_arg
                                                             in
                                                          [uu____7366]  in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7364
                                                          uu____7365
                                                         in
                                                      uu____7359
                                                        FStar_Pervasives_Native.None
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7406 =
                                                          let uu____7411 =
                                                            let uu____7412 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7412
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          let uu____7421 =
                                                            let uu____7422 =
                                                              let uu____7425
                                                                =
                                                                let uu____7428
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a
                                                                   in
                                                                let uu____7429
                                                                  =
                                                                  let uu____7432
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                  let uu____7433
                                                                    =
                                                                    let uu____7436
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                    let uu____7437
                                                                    =
                                                                    let uu____7440
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7440]
                                                                     in
                                                                    uu____7436
                                                                    ::
                                                                    uu____7437
                                                                     in
                                                                  uu____7432
                                                                    ::
                                                                    uu____7433
                                                                   in
                                                                uu____7428 ::
                                                                  uu____7429
                                                                 in
                                                              r :: uu____7425
                                                               in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____7422
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7411
                                                            uu____7421
                                                           in
                                                        uu____7406
                                                          FStar_Pervasives_Native.None
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7458 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7458
                                                      then
                                                        let uu____7469 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7476 =
                                                          let uu____7485 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7485]  in
                                                        uu____7469 ::
                                                          uu____7476
                                                      else []  in
                                                    let k =
                                                      let uu____7521 =
                                                        let uu____7530 =
                                                          let uu____7539 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____7546 =
                                                            let uu____7555 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____7555]  in
                                                          uu____7539 ::
                                                            uu____7546
                                                           in
                                                        let uu____7580 =
                                                          let uu____7589 =
                                                            let uu____7598 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____7605 =
                                                              let uu____7614
                                                                =
                                                                let uu____7621
                                                                  =
                                                                  let uu____7622
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____7622
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7621
                                                                 in
                                                              let uu____7623
                                                                =
                                                                let uu____7632
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____7639
                                                                  =
                                                                  let uu____7648
                                                                    =
                                                                    let uu____7655
                                                                    =
                                                                    let uu____7656
                                                                    =
                                                                    let uu____7665
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7665]
                                                                     in
                                                                    let uu____7684
                                                                    =
                                                                    let uu____7687
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7687
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7656
                                                                    uu____7684
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7655
                                                                     in
                                                                  [uu____7648]
                                                                   in
                                                                uu____7632 ::
                                                                  uu____7639
                                                                 in
                                                              uu____7614 ::
                                                                uu____7623
                                                               in
                                                            uu____7598 ::
                                                              uu____7605
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7589
                                                           in
                                                        FStar_List.append
                                                          uu____7530
                                                          uu____7580
                                                         in
                                                      let uu____7732 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7521 uu____7732
                                                       in
                                                    let uu____7735 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____7735 with
                                                     | (k1,uu____7743,uu____7744)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___778_7754
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.is_native_tactic
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.is_native_tactic);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___778_7754.FStar_TypeChecker_Env.erasable_types_tab)
                                                              })
                                                             (fun _7756  ->
                                                                FStar_Pervasives_Native.Some
                                                                  _7756)
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
                                              (let uu____7783 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____7797 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____7797 with
                                                    | (usubst,uvs) ->
                                                        let uu____7820 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____7821 =
                                                          let uu___791_7822 =
                                                            act  in
                                                          let uu____7823 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____7824 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___791_7822.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___791_7822.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___791_7822.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____7823;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____7824
                                                          }  in
                                                        (uu____7820,
                                                          uu____7821))
                                                  in
                                               match uu____7783 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____7828 =
                                                       let uu____7829 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____7829.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____7828 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____7855 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____7855
                                                         then
                                                           let uu____7858 =
                                                             let uu____7861 =
                                                               let uu____7862
                                                                 =
                                                                 let uu____7863
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____7863
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____7862
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____7861
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7858
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____7886 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____7887 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____7887 with
                                                    | (act_typ1,uu____7895,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___808_7898 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.is_native_tactic
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.is_native_tactic);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___808_7898.FStar_TypeChecker_Env.erasable_types_tab)
                                                          }  in
                                                        ((let uu____7901 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____7901
                                                          then
                                                            let uu____7905 =
                                                              FStar_Ident.text_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____7907 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____7909 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____7905
                                                              uu____7907
                                                              uu____7909
                                                          else ());
                                                         (let uu____7914 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____7914
                                                          with
                                                          | (act_defn,uu____7922,g_a)
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
                                                              let uu____7926
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
                                                                    let uu____7962
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____7962
                                                                    with
                                                                    | 
                                                                    (bs2,uu____7974)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____7981
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7981
                                                                     in
                                                                    let uu____7984
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____7984
                                                                    with
                                                                    | 
                                                                    (k1,uu____7998,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8002
                                                                    ->
                                                                    let uu____8003
                                                                    =
                                                                    let uu____8009
                                                                    =
                                                                    let uu____8011
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8013
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8011
                                                                    uu____8013
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8009)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8003
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____7926
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
                                                                    let uu____8031
                                                                    =
                                                                    let uu____8032
                                                                    =
                                                                    let uu____8033
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8033
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8032
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8031);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8035
                                                                    =
                                                                    let uu____8036
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8036.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8035
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8061
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8061
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8068
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8068
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8088
                                                                    =
                                                                    let uu____8089
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8089]
                                                                     in
                                                                    let uu____8090
                                                                    =
                                                                    let uu____8101
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8101]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8088;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8090;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8126
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8126))
                                                                    | 
                                                                    uu____8129
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8131
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8153
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8153))
                                                                     in
                                                                    match uu____8131
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
                                                                    let uu___858_8172
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___858_8172.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___858_8172.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___858_8172.FStar_Syntax_Syntax.action_params);
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
                                match uu____6610 with
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
                                      let uu____8215 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8215 ts1
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
                                          uu____8227 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8228 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8229 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___878_8232 = ed2  in
                                      let uu____8233 = cl signature  in
                                      let uu____8234 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___881_8242 = a  in
                                             let uu____8243 =
                                               let uu____8244 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8244
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8269 =
                                               let uu____8270 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8270
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___881_8242.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___881_8242.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___881_8242.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___881_8242.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8243;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8269
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___878_8232.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___878_8232.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___878_8232.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___878_8232.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8233;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8234;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___878_8232.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8296 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8296
                                      then
                                        let uu____8301 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8301
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
        let uu____8327 =
          let uu____8342 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8342 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8327 env ed quals
  
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
        let fail1 uu____8392 =
          let uu____8393 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8399 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8393 uu____8399  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8443)::(wp,uu____8445)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8474 -> fail1 ())
        | uu____8475 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8488 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8488
       then
         let uu____8493 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8493
       else ());
      (let uu____8498 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____8498 with
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
             let uu____8531 =
               ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
                  (let uu____8535 =
                     let uu____8536 =
                       FStar_All.pipe_right src_ed
                         FStar_Syntax_Util.get_layered_effect_base
                        in
                     FStar_All.pipe_right uu____8536 FStar_Util.must  in
                   FStar_Ident.lid_equals uu____8535
                     tgt_ed.FStar_Syntax_Syntax.mname))
                 ||
                 (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered)
                     &&
                     (let uu____8545 =
                        let uu____8546 =
                          FStar_All.pipe_right tgt_ed
                            FStar_Syntax_Util.get_layered_effect_base
                           in
                        FStar_All.pipe_right uu____8546 FStar_Util.must  in
                      FStar_Ident.lid_equals uu____8545
                        src_ed.FStar_Syntax_Syntax.mname))
                    &&
                    (let uu____8554 =
                       FStar_Ident.lid_equals
                         src_ed.FStar_Syntax_Syntax.mname
                         FStar_Parser_Const.effect_PURE_lid
                        in
                     Prims.op_Negation uu____8554))
                in
             if uu____8531
             then
               let uu____8557 =
                 let uu____8563 =
                   let uu____8565 =
                     FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   let uu____8568 =
                     FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   FStar_Util.format2
                     "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                     uu____8565 uu____8568
                    in
                 (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8563)  in
               FStar_Errors.raise_error uu____8557 r
             else ());
            (let uu____8575 =
               if (FStar_List.length us) = Prims.int_zero
               then (env0, us, lift)
               else
                 (let uu____8599 = FStar_Syntax_Subst.open_univ_vars us lift
                     in
                  match uu____8599 with
                  | (us1,lift1) ->
                      let uu____8614 =
                        FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                      (uu____8614, us1, lift1))
                in
             match uu____8575 with
             | (env,us1,lift1) ->
                 let uu____8624 =
                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                 (match uu____8624 with
                  | (lift2,lc,g) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env g;
                       (let lift_ty =
                          FStar_All.pipe_right
                            lc.FStar_TypeChecker_Common.res_typ
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta] env0)
                           in
                        (let uu____8637 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "LayeredEffects")
                            in
                         if uu____8637
                         then
                           let uu____8642 =
                             FStar_Syntax_Print.term_to_string lift2  in
                           let uu____8644 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.print2
                             "Typechecked lift: %s and lift_ty: %s\n"
                             uu____8642 uu____8644
                         else ());
                        (let lift_t_shape_error s =
                           let uu____8658 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.source
                              in
                           let uu____8660 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.target
                              in
                           let uu____8662 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.format4
                             "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                             uu____8658 uu____8660 s uu____8662
                            in
                         let uu____8665 =
                           let uu____8672 =
                             let uu____8677 = FStar_Syntax_Util.type_u ()  in
                             FStar_All.pipe_right uu____8677
                               (fun uu____8694  ->
                                  match uu____8694 with
                                  | (t,u) ->
                                      let uu____8705 =
                                        let uu____8706 =
                                          FStar_Syntax_Syntax.gen_bv "a"
                                            FStar_Pervasives_Native.None t
                                           in
                                        FStar_All.pipe_right uu____8706
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____8705, u))
                              in
                           match uu____8672 with
                           | (a,u_a) ->
                               let rest_bs =
                                 let uu____8725 =
                                   let uu____8726 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____8726.FStar_Syntax_Syntax.n  in
                                 match uu____8725 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____8738) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____8766 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____8766 with
                                      | (a',uu____8776)::bs1 ->
                                          let uu____8796 =
                                            let uu____8797 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one))
                                               in
                                            FStar_All.pipe_right uu____8797
                                              FStar_Pervasives_Native.fst
                                             in
                                          let uu____8895 =
                                            let uu____8908 =
                                              let uu____8911 =
                                                let uu____8912 =
                                                  let uu____8919 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____8919)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____8912
                                                 in
                                              [uu____8911]  in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____8908
                                             in
                                          FStar_All.pipe_right uu____8796
                                            uu____8895)
                                 | uu____8934 ->
                                     let uu____8935 =
                                       let uu____8941 =
                                         lift_t_shape_error
                                           "either not an arrow, or not enough binders"
                                          in
                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                         uu____8941)
                                        in
                                     FStar_Errors.raise_error uu____8935 r
                                  in
                               let uu____8953 =
                                 let uu____8964 =
                                   let uu____8969 =
                                     FStar_TypeChecker_Env.push_binders env
                                       (a :: rest_bs)
                                      in
                                   let uu____8976 =
                                     let uu____8977 =
                                       FStar_All.pipe_right a
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8977
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   FStar_TypeChecker_Util.fresh_effect_repr_en
                                     uu____8969 r
                                     sub1.FStar_Syntax_Syntax.source u_a
                                     uu____8976
                                    in
                                 match uu____8964 with
                                 | (f_sort,g1) ->
                                     let uu____8998 =
                                       let uu____9005 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None
                                           f_sort
                                          in
                                       FStar_All.pipe_right uu____9005
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____8998, g1)
                                  in
                               (match uu____8953 with
                                | (f_b,g_f_b) ->
                                    let bs = a ::
                                      (FStar_List.append rest_bs [f_b])  in
                                    let uu____9072 =
                                      let uu____9077 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9078 =
                                        let uu____9079 =
                                          FStar_All.pipe_right a
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____9079
                                          FStar_Syntax_Syntax.bv_to_name
                                         in
                                      FStar_TypeChecker_Util.fresh_effect_repr_en
                                        uu____9077 r
                                        sub1.FStar_Syntax_Syntax.target u_a
                                        uu____9078
                                       in
                                    (match uu____9072 with
                                     | (repr,g_repr) ->
                                         let uu____9096 =
                                           let uu____9099 =
                                             let uu____9102 =
                                               let uu____9105 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               FStar_All.pipe_right
                                                 uu____9105
                                                 (fun _9108  ->
                                                    FStar_Pervasives_Native.Some
                                                      _9108)
                                                in
                                             FStar_Syntax_Syntax.mk_Total'
                                               repr uu____9102
                                              in
                                           FStar_Syntax_Util.arrow bs
                                             uu____9099
                                            in
                                         let uu____9109 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g_f_b g_repr
                                            in
                                         (uu____9096, uu____9109)))
                            in
                         match uu____8665 with
                         | (k,g_k) ->
                             ((let uu____9119 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____9119
                               then
                                 let uu____9124 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "tc_layered_lift: before unification k: %s\n"
                                   uu____9124
                               else ());
                              (let g1 =
                                 FStar_TypeChecker_Rel.teq env lift_ty k  in
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g_k;
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g1;
                               (let uu____9133 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____9133
                                then
                                  let uu____9138 =
                                    FStar_Syntax_Print.term_to_string k  in
                                  FStar_Util.print1
                                    "After unification k: %s\n" uu____9138
                                else ());
                               (let uu____9143 =
                                  let uu____9156 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 lift2
                                     in
                                  match uu____9156 with
                                  | (inst_us,lift3) ->
                                      (if
                                         (FStar_List.length inst_us) <>
                                           Prims.int_one
                                       then
                                         (let uu____9183 =
                                            let uu____9189 =
                                              let uu____9191 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____9193 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____9195 =
                                                let uu____9197 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____9197
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____9204 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format4
                                                "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                                uu____9191 uu____9193
                                                uu____9195 uu____9204
                                               in
                                            (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                              uu____9189)
                                             in
                                          FStar_Errors.raise_error uu____9183
                                            r)
                                       else ();
                                       (let uu____9210 =
                                          ((FStar_List.length us1) =
                                             Prims.int_zero)
                                            ||
                                            (((FStar_List.length us1) =
                                                (FStar_List.length inst_us))
                                               &&
                                               (FStar_List.forall2
                                                  (fun u1  ->
                                                     fun u2  ->
                                                       let uu____9219 =
                                                         FStar_Syntax_Syntax.order_univ_name
                                                           u1 u2
                                                          in
                                                       uu____9219 =
                                                         Prims.int_zero) us1
                                                  inst_us))
                                           in
                                        if uu____9210
                                        then
                                          let uu____9236 =
                                            let uu____9239 =
                                              FStar_All.pipe_right k
                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                   env)
                                               in
                                            FStar_All.pipe_right uu____9239
                                              (FStar_Syntax_Subst.close_univ_vars
                                                 inst_us)
                                             in
                                          (inst_us, lift3, uu____9236)
                                        else
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
                                                   FStar_All.pipe_right us1
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9264
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9271 =
                                                 let uu____9273 =
                                                   FStar_All.pipe_right
                                                     inst_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9273
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9280 =
                                                 FStar_Syntax_Print.term_to_string
                                                   lift3
                                                  in
                                               FStar_Util.format5
                                                 "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                 uu____9258 uu____9260
                                                 uu____9262 uu____9271
                                                 uu____9280
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____9256)
                                              in
                                           FStar_Errors.raise_error
                                             uu____9250 r)))
                                   in
                                match uu____9143 with
                                | (us2,lift3,lift_wp) ->
                                    let sub2 =
                                      let uu___989_9312 = sub1  in
                                      {
                                        FStar_Syntax_Syntax.source =
                                          (uu___989_9312.FStar_Syntax_Syntax.source);
                                        FStar_Syntax_Syntax.target =
                                          (uu___989_9312.FStar_Syntax_Syntax.target);
                                        FStar_Syntax_Syntax.lift_wp =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift_wp));
                                        FStar_Syntax_Syntax.lift =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift3))
                                      }  in
                                    ((let uu____9322 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env0)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____9322
                                      then
                                        let uu____9327 =
                                          FStar_Syntax_Print.sub_eff_to_string
                                            sub2
                                           in
                                        FStar_Util.print1
                                          "Final sub_effect: %s\n" uu____9327
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
        let check_and_gen1 env1 t k =
          let uu____9364 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k  in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9364  in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____9367 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9367
        then tc_layered_lift env sub1
        else
          (let uu____9374 =
             let uu____9381 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9381
              in
           match uu____9374 with
           | (a,wp_a_src) ->
               let uu____9388 =
                 let uu____9395 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9395
                  in
               (match uu____9388 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9403 =
                        let uu____9406 =
                          let uu____9407 =
                            let uu____9414 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9414)  in
                          FStar_Syntax_Syntax.NT uu____9407  in
                        [uu____9406]  in
                      FStar_Syntax_Subst.subst uu____9403 wp_b_tgt  in
                    let expected_k =
                      let uu____9422 =
                        let uu____9431 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9438 =
                          let uu____9447 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9447]  in
                        uu____9431 :: uu____9438  in
                      let uu____9472 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9422 uu____9472  in
                    let repr_type eff_name a1 wp =
                      (let uu____9494 =
                         let uu____9496 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9496  in
                       if uu____9494
                       then
                         let uu____9499 =
                           let uu____9505 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9505)
                            in
                         let uu____9509 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9499 uu____9509
                       else ());
                      (let uu____9512 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9512 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9545 =
                               let uu____9546 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9546
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9545
                              in
                           let uu____9553 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9554 =
                             let uu____9561 =
                               let uu____9562 =
                                 let uu____9579 =
                                   let uu____9590 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9599 =
                                     let uu____9610 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9610]  in
                                   uu____9590 :: uu____9599  in
                                 (repr, uu____9579)  in
                               FStar_Syntax_Syntax.Tm_app uu____9562  in
                             FStar_Syntax_Syntax.mk uu____9561  in
                           uu____9554 FStar_Pervasives_Native.None uu____9553)
                       in
                    let uu____9655 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9828 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9839 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9839 with
                              | (usubst,uvs1) ->
                                  let uu____9862 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____9863 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____9862, uu____9863)
                            else (env, lift_wp)  in
                          (match uu____9828 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____9913 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____9913))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____9984 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____9999 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____9999 with
                              | (usubst,uvs) ->
                                  let uu____10024 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____10024)
                            else ([], lift)  in
                          (match uu____9984 with
                           | (uvs,lift1) ->
                               ((let uu____10060 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10060
                                 then
                                   let uu____10064 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10064
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10070 =
                                   let uu____10077 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10077 lift1
                                    in
                                 match uu____10070 with
                                 | (lift2,comp,uu____10102) ->
                                     let uu____10103 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10103 with
                                      | (uu____10132,lift_wp,lift_elab) ->
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
                                            let uu____10164 =
                                              let uu____10175 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10175
                                               in
                                            let uu____10192 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10164, uu____10192)
                                          else
                                            (let uu____10221 =
                                               let uu____10232 =
                                                 let uu____10241 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10241)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10232
                                                in
                                             let uu____10256 =
                                               let uu____10265 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10265)  in
                                             (uu____10221, uu____10256))))))
                       in
                    (match uu____9655 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1073_10329 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1073_10329.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1073_10329.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1073_10329.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1073_10329.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1073_10329.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1073_10329.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1073_10329.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1073_10329.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1073_10329.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1073_10329.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1073_10329.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1073_10329.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1073_10329.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1073_10329.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1073_10329.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1073_10329.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1073_10329.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1073_10329.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1073_10329.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1073_10329.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1073_10329.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1073_10329.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1073_10329.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1073_10329.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1073_10329.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1073_10329.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1073_10329.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1073_10329.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1073_10329.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1073_10329.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1073_10329.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1073_10329.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1073_10329.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1073_10329.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1073_10329.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1073_10329.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1073_10329.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1073_10329.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1073_10329.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1073_10329.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1073_10329.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1073_10329.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1073_10329.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1073_10329.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10362 =
                                 let uu____10367 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10367 with
                                 | (usubst,uvs1) ->
                                     let uu____10390 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10391 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10390, uu____10391)
                                  in
                               (match uu____10362 with
                                | (env2,lift2) ->
                                    let uu____10396 =
                                      let uu____10403 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10403
                                       in
                                    (match uu____10396 with
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
                                             let uu____10429 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10430 =
                                               let uu____10437 =
                                                 let uu____10438 =
                                                   let uu____10455 =
                                                     let uu____10466 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10475 =
                                                       let uu____10486 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10486]  in
                                                     uu____10466 ::
                                                       uu____10475
                                                      in
                                                   (lift_wp1, uu____10455)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10438
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10437
                                                in
                                             uu____10430
                                               FStar_Pervasives_Native.None
                                               uu____10429
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10534 =
                                             let uu____10543 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10550 =
                                               let uu____10559 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10566 =
                                                 let uu____10575 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10575]  in
                                               uu____10559 :: uu____10566  in
                                             uu____10543 :: uu____10550  in
                                           let uu____10606 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10534 uu____10606
                                            in
                                         let uu____10609 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10609 with
                                          | (expected_k2,uu____10619,uu____10620)
                                              ->
                                              let lift3 =
                                                if
                                                  (FStar_List.length uvs) =
                                                    Prims.int_zero
                                                then
                                                  check_and_gen1 env2 lift2
                                                    expected_k2
                                                else
                                                  (let lift3 =
                                                     FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                                       env2 lift2 expected_k2
                                                      in
                                                   let uu____10628 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10628))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10636 =
                             let uu____10638 =
                               let uu____10640 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10640
                                 FStar_List.length
                                in
                             uu____10638 <> Prims.int_one  in
                           if uu____10636
                           then
                             let uu____10663 =
                               let uu____10669 =
                                 let uu____10671 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10673 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10675 =
                                   let uu____10677 =
                                     let uu____10679 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10679
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10677
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10671 uu____10673 uu____10675
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10669)
                                in
                             FStar_Errors.raise_error uu____10663 r
                           else ());
                          (let uu____10706 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10709 =
                                  let uu____10711 =
                                    let uu____10714 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10714
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10711
                                    FStar_List.length
                                   in
                                uu____10709 <> Prims.int_one)
                              in
                           if uu____10706
                           then
                             let uu____10753 =
                               let uu____10759 =
                                 let uu____10761 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10763 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10765 =
                                   let uu____10767 =
                                     let uu____10769 =
                                       let uu____10772 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10772
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10769
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10767
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10761 uu____10763 uu____10765
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10759)
                                in
                             FStar_Errors.raise_error uu____10753 r
                           else ());
                          (let uu___1110_10814 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1110_10814.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1110_10814.FStar_Syntax_Syntax.target);
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
    fun uu____10845  ->
      fun r  ->
        match uu____10845 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____10868 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10896 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____10896 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____10927 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____10927 c  in
                     let uu____10936 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____10936, uvs1, tps1, c1))
               in
            (match uu____10868 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____10956 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____10956 with
                  | (tps2,c2) ->
                      let uu____10971 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____10971 with
                       | (tps3,env3,us) ->
                           let uu____10989 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____10989 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____11015)::uu____11016 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____11035 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____11043 =
                                    let uu____11045 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____11045  in
                                  if uu____11043
                                  then
                                    let uu____11048 =
                                      let uu____11054 =
                                        let uu____11056 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11058 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11056 uu____11058
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11054)
                                       in
                                    FStar_Errors.raise_error uu____11048 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11066 =
                                    let uu____11067 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11067
                                     in
                                  match uu____11066 with
                                  | (uvs2,t) ->
                                      let uu____11096 =
                                        let uu____11101 =
                                          let uu____11114 =
                                            let uu____11115 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11115.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11114)  in
                                        match uu____11101 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11130,c5)) -> ([], c5)
                                        | (uu____11172,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11211 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11096 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11243 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11243 with
                                               | (uu____11248,t1) ->
                                                   let uu____11250 =
                                                     let uu____11256 =
                                                       let uu____11258 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11260 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11264 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11258
                                                         uu____11260
                                                         uu____11264
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11256)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11250 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  
let (tc_polymonadic_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme ->
            (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.tscheme))
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun ts  ->
            let eff_name =
              let uu____11306 = FStar_Ident.string_of_lid m  in
              let uu____11308 = FStar_Ident.string_of_lid n1  in
              let uu____11310 = FStar_Ident.string_of_lid p  in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11306 uu____11308
                uu____11310
               in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
               in
            (let uu____11319 =
               FStar_TypeChecker_Env.is_user_reifiable_effect env p  in
             if uu____11319
             then
               let uu____11322 =
                 let uu____11328 =
                   let uu____11330 = FStar_Ident.string_of_lid p  in
                   FStar_Util.format2
                     "Error typechecking the polymonadic bind %s, the final effect %s is reifiable and reification of polymondic binds is not yet implemented"
                     eff_name uu____11330
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____11328)  in
               FStar_Errors.raise_error uu____11322 r
             else ());
            (let uu____11336 =
               check_and_gen env eff_name "polymonadic_bind"
                 (Prims.of_int (2)) ts
                in
             match uu____11336 with
             | (us,t,ty) ->
                 let uu____11352 = FStar_Syntax_Subst.open_univ_vars us ty
                    in
                 (match uu____11352 with
                  | (us1,ty1) ->
                      let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                         in
                      let uu____11364 =
                        let uu____11369 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____11369
                          (fun uu____11386  ->
                             match uu____11386 with
                             | (t1,u) ->
                                 let uu____11397 =
                                   let uu____11398 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t1
                                      in
                                   FStar_All.pipe_right uu____11398
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____11397, u))
                         in
                      (match uu____11364 with
                       | (a,u_a) ->
                           let uu____11406 =
                             let uu____11411 = FStar_Syntax_Util.type_u ()
                                in
                             FStar_All.pipe_right uu____11411
                               (fun uu____11428  ->
                                  match uu____11428 with
                                  | (t1,u) ->
                                      let uu____11439 =
                                        let uu____11440 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1
                                           in
                                        FStar_All.pipe_right uu____11440
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11439, u))
                              in
                           (match uu____11406 with
                            | (b,u_b) ->
                                let rest_bs =
                                  let uu____11457 =
                                    let uu____11458 =
                                      FStar_Syntax_Subst.compress ty1  in
                                    uu____11458.FStar_Syntax_Syntax.n  in
                                  match uu____11457 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____11470) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____11498 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____11498 with
                                       | (a',uu____11508)::(b',uu____11510)::bs1
                                           ->
                                           let uu____11540 =
                                             let uu____11541 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2))))
                                                in
                                             FStar_All.pipe_right uu____11541
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____11639 =
                                             let uu____11652 =
                                               let uu____11655 =
                                                 let uu____11656 =
                                                   let uu____11663 =
                                                     let uu____11666 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____11666
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   (a', uu____11663)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11656
                                                  in
                                               let uu____11679 =
                                                 let uu____11682 =
                                                   let uu____11683 =
                                                     let uu____11690 =
                                                       let uu____11693 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____11693
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     (b', uu____11690)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11683
                                                    in
                                                 [uu____11682]  in
                                               uu____11655 :: uu____11679  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11652
                                              in
                                           FStar_All.pipe_right uu____11540
                                             uu____11639)
                                  | uu____11714 ->
                                      let uu____11715 =
                                        let uu____11721 =
                                          let uu____11723 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1
                                             in
                                          let uu____11725 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1
                                             in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11723 uu____11725
                                           in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11721)
                                         in
                                      FStar_Errors.raise_error uu____11715 r
                                   in
                                let bs = a :: b :: rest_bs  in
                                let uu____11758 =
                                  let uu____11769 =
                                    let uu____11774 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs
                                       in
                                    let uu____11775 =
                                      let uu____11776 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11776
                                        FStar_Syntax_Syntax.bv_to_name
                                       in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____11774 r m u_a uu____11775
                                     in
                                  match uu____11769 with
                                  | (repr,g) ->
                                      let uu____11797 =
                                        let uu____11804 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr
                                           in
                                        FStar_All.pipe_right uu____11804
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11797, g)
                                   in
                                (match uu____11758 with
                                 | (f,guard_f) ->
                                     let uu____11836 =
                                       let x_a =
                                         let uu____11854 =
                                           let uu____11855 =
                                             let uu____11856 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____11856
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____11855
                                            in
                                         FStar_All.pipe_right uu____11854
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       let uu____11872 =
                                         let uu____11877 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a])
                                            in
                                         let uu____11896 =
                                           let uu____11897 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____11897
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____11877 r n1 u_b uu____11896
                                          in
                                       match uu____11872 with
                                       | (repr,g) ->
                                           let uu____11918 =
                                             let uu____11925 =
                                               let uu____11926 =
                                                 let uu____11927 =
                                                   let uu____11930 =
                                                     let uu____11933 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         ()
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____11933
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____11930
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____11927
                                                  in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____11926
                                                in
                                             FStar_All.pipe_right uu____11925
                                               FStar_Syntax_Syntax.mk_binder
                                              in
                                           (uu____11918, g)
                                        in
                                     (match uu____11836 with
                                      | (g,guard_g) ->
                                          let uu____11977 =
                                            let uu____11982 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs
                                               in
                                            let uu____11983 =
                                              let uu____11984 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right
                                                uu____11984
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____11982 r p u_b uu____11983
                                             in
                                          (match uu____11977 with
                                           | (repr,guard_repr) ->
                                               let k =
                                                 let uu____12002 =
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr
                                                     (FStar_Pervasives_Native.Some
                                                        u_b)
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   (FStar_List.append bs
                                                      [f; g]) uu____12002
                                                  in
                                               let guard_eq =
                                                 FStar_TypeChecker_Rel.teq
                                                   env1 ty1 k
                                                  in
                                               (FStar_List.iter
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env1)
                                                  [guard_f;
                                                  guard_g;
                                                  guard_repr;
                                                  guard_eq];
                                                (let uu____12032 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     FStar_Options.Extreme
                                                    in
                                                 if uu____12032
                                                 then
                                                   let uu____12036 =
                                                     FStar_Syntax_Print.tscheme_to_string
                                                       (us1, t)
                                                      in
                                                   let uu____12042 =
                                                     FStar_Syntax_Print.tscheme_to_string
                                                       (us1, k)
                                                      in
                                                   FStar_Util.print3
                                                     "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                     eff_name uu____12036
                                                     uu____12042
                                                 else ());
                                                (let uu____12051 =
                                                   let uu____12052 =
                                                     let uu____12055 =
                                                       FStar_All.pipe_right k
                                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                            env1)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____12055
                                                       (FStar_Syntax_Subst.close_univ_vars
                                                          us1)
                                                      in
                                                   (us1, uu____12052)  in
                                                 ((us1, t), uu____12051))))))))))
  