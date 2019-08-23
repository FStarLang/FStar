open Prims
let (dmff_cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  = fun env  -> fun ed  -> FStar_TypeChecker_DMFF.cps_and_elaborate env ed 
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____32 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____32
       then
         let uu____37 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking layered effect: \n\t%s\n" uu____37
       else ());
      if
        ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
          ||
          ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
             Prims.int_zero)
      then
        (let uu____55 = FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname
            in
         FStar_Errors.raise_error
           (FStar_Errors.Fatal_UnexpectedEffect,
             (Prims.op_Hat "Binders are not supported for layered effects ("
                (Prims.op_Hat (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                   ")"))) uu____55)
      else ();
      (let check_and_gen' comb n1 env_opt uu____95 =
         match uu____95 with
         | (us,t) ->
             let env =
               if FStar_Util.is_some env_opt
               then FStar_All.pipe_right env_opt FStar_Util.must
               else env0  in
             let uu____124 = FStar_Syntax_Subst.open_univ_vars us t  in
             (match uu____124 with
              | (us1,t1) ->
                  let uu____137 =
                    let uu____142 =
                      let uu____149 =
                        FStar_TypeChecker_Env.push_univ_vars env us1  in
                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term uu____149
                        t1
                       in
                    match uu____142 with
                    | (t2,lc,g) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (t2, (lc.FStar_TypeChecker_Common.res_typ)))
                     in
                  (match uu____137 with
                   | (t2,ty) ->
                       let uu____166 =
                         FStar_TypeChecker_Util.generalize_universes env t2
                          in
                       (match uu____166 with
                        | (g_us,t3) ->
                            let ty1 =
                              FStar_Syntax_Subst.close_univ_vars g_us ty  in
                            (if (FStar_List.length g_us) <> n1
                             then
                               (let error =
                                  let uu____189 = FStar_Util.string_of_int n1
                                     in
                                  let uu____191 =
                                    let uu____193 =
                                      FStar_All.pipe_right g_us
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____193
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format4
                                    "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                    comb uu____189 uu____191
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                    error) t3.FStar_Syntax_Syntax.pos)
                             else ();
                             (match us1 with
                              | [] -> (g_us, t3, ty1)
                              | uu____210 ->
                                  let uu____211 =
                                    ((FStar_List.length us1) =
                                       (FStar_List.length g_us))
                                      &&
                                      (FStar_List.forall2
                                         (fun u1  ->
                                            fun u2  ->
                                              let uu____218 =
                                                FStar_Syntax_Syntax.order_univ_name
                                                  u1 u2
                                                 in
                                              uu____218 = Prims.int_zero) us1
                                         g_us)
                                     in
                                  if uu____211
                                  then (g_us, t3, ty1)
                                  else
                                    (let uu____231 =
                                       let uu____237 =
                                         let uu____239 =
                                           FStar_Util.string_of_int
                                             (FStar_List.length us1)
                                            in
                                         let uu____241 =
                                           FStar_Util.string_of_int
                                             (FStar_List.length g_us)
                                            in
                                         FStar_Util.format4
                                           "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                           (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                           comb uu____239 uu____241
                                          in
                                       (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                         uu____237)
                                        in
                                     FStar_Errors.raise_error uu____231
                                       t3.FStar_Syntax_Syntax.pos))))))
          in
       let log_combinator s uu____274 =
         match uu____274 with
         | (us,t,ty) ->
             let uu____303 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffects")
                in
             if uu____303
             then
               let uu____308 = FStar_Syntax_Print.tscheme_to_string (us, t)
                  in
               let uu____314 = FStar_Syntax_Print.tscheme_to_string (us, ty)
                  in
               FStar_Util.print4 "Typechecked %s:%s = %s:%s\n"
                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str s uu____308
                 uu____314
             else ()
          in
       let fresh_a_and_u_a a =
         let uu____335 = FStar_Syntax_Util.type_u ()  in
         FStar_All.pipe_right uu____335
           (fun uu____352  ->
              match uu____352 with
              | (t,u) ->
                  let uu____363 =
                    let uu____364 =
                      FStar_Syntax_Syntax.gen_bv a
                        FStar_Pervasives_Native.None t
                       in
                    FStar_All.pipe_right uu____364
                      FStar_Syntax_Syntax.mk_binder
                     in
                  (uu____363, u))
          in
       let fresh_x_a x a =
         let uu____378 =
           let uu____379 =
             let uu____380 =
               FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
             FStar_All.pipe_right uu____380 FStar_Syntax_Syntax.bv_to_name
              in
           FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
             uu____379
            in
         FStar_All.pipe_right uu____378 FStar_Syntax_Syntax.mk_binder  in
       let signature =
         let r =
           (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
            in
         let uu____407 =
           check_and_gen' "signature" Prims.int_one
             FStar_Pervasives_Native.None ed.FStar_Syntax_Syntax.signature
            in
         match uu____407 with
         | (sig_us,sig_t,sig_ty) ->
             let uu____431 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                in
             (match uu____431 with
              | (us,t) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us  in
                  let uu____451 = fresh_a_and_u_a "a"  in
                  (match uu____451 with
                   | (a,u) ->
                       let rest_bs =
                         let uu____472 =
                           let uu____473 =
                             FStar_All.pipe_right a
                               FStar_Pervasives_Native.fst
                              in
                           FStar_All.pipe_right uu____473
                             FStar_Syntax_Syntax.bv_to_name
                            in
                         FStar_TypeChecker_Util.layered_effect_indices_as_binders
                           (sig_us, sig_t) u uu____472
                          in
                       let bs = a :: rest_bs  in
                       let k =
                         let uu____504 =
                           FStar_Syntax_Syntax.mk_Total
                             FStar_Syntax_Syntax.teff
                            in
                         FStar_Syntax_Util.arrow bs uu____504  in
                       let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                       (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                        (let uu____509 =
                           let uu____512 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta] env k
                              in
                           FStar_Syntax_Subst.close_univ_vars us uu____512
                            in
                         (sig_us, uu____509, sig_ty)))))
          in
       log_combinator "signature" signature;
       (let repr =
          let r =
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.pos
             in
          let uu____539 =
            check_and_gen' "repr" Prims.int_one FStar_Pervasives_Native.None
              ed.FStar_Syntax_Syntax.repr
             in
          match uu____539 with
          | (repr_us,repr_t,repr_ty) ->
              let uu____563 =
                FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
              (match uu____563 with
               | (us,ty) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us  in
                   let uu____583 = fresh_a_and_u_a "a"  in
                   (match uu____583 with
                    | (a,u) ->
                        let rest_bs =
                          let signature_ts =
                            let uu____605 = signature  in
                            match uu____605 with
                            | (us1,t,uu____620) -> (us1, t)  in
                          let uu____637 =
                            let uu____638 =
                              FStar_All.pipe_right a
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____638
                              FStar_Syntax_Syntax.bv_to_name
                             in
                          FStar_TypeChecker_Util.layered_effect_indices_as_binders
                            signature_ts u uu____637
                           in
                        let bs = a :: rest_bs  in
                        let k =
                          let uu____665 =
                            let uu____668 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_right uu____668
                              (fun uu____680  ->
                                 match uu____680 with
                                 | (t,u1) ->
                                     FStar_Syntax_Syntax.mk_Total' t
                                       (FStar_Pervasives_Native.Some u1))
                             in
                          FStar_Syntax_Util.arrow bs uu____665  in
                        let g = FStar_TypeChecker_Rel.teq env ty k  in
                        (FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____689 =
                            let uu____692 =
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Env.Beta] env k
                               in
                            FStar_Syntax_Subst.close_univ_vars us uu____692
                             in
                          (repr_us, repr_t, uu____689)))))
           in
        log_combinator "repr" repr;
        (let fresh_repr r env u a_tm =
           let signature_ts =
             let uu____727 = signature  in
             match uu____727 with | (us,t,uu____742) -> (us, t)  in
           let repr_ts =
             let uu____760 = repr  in
             match uu____760 with | (us,t,uu____775) -> (us, t)  in
           FStar_TypeChecker_Util.fresh_layered_effect_repr env r
             ed.FStar_Syntax_Syntax.mname signature_ts repr_ts u a_tm
            in
         let return_repr =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
              in
           let uu____810 =
             check_and_gen' "return_repr" Prims.int_one
               FStar_Pervasives_Native.None
               ed.FStar_Syntax_Syntax.return_repr
              in
           match uu____810 with
           | (ret_us,ret_t,ret_ty) ->
               let uu____834 =
                 FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
               (match uu____834 with
                | (us,ty) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____854 = fresh_a_and_u_a "a"  in
                    (match uu____854 with
                     | (a,u_a) ->
                         let rest_bs =
                           let uu____883 =
                             let uu____884 = FStar_Syntax_Subst.compress ty
                                in
                             uu____884.FStar_Syntax_Syntax.n  in
                           match uu____883 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,uu____896) when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____924 =
                                 FStar_Syntax_Subst.open_binders bs  in
                               (match uu____924 with
                                | (a',uu____934)::bs1 ->
                                    let uu____954 =
                                      FStar_List.splitAt
                                        ((FStar_List.length bs1) -
                                           Prims.int_one) bs1
                                       in
                                    (match uu____954 with
                                     | (bs2,uu____997) ->
                                         let substs =
                                           let uu____1033 =
                                             let uu____1034 =
                                               let uu____1041 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   (FStar_Pervasives_Native.fst
                                                      a)
                                                  in
                                               (a', uu____1041)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____1034
                                              in
                                           [uu____1033]  in
                                         FStar_Syntax_Subst.subst_binders
                                           substs bs2)
                                | uu____1048 -> failwith "Impossible!")
                           | uu____1058 ->
                               FStar_Errors.raise_error
                                 (FStar_Errors.Fatal_UnexpectedEffect, "") r
                            in
                         let bs =
                           let uu____1078 =
                             let uu____1087 =
                               let uu____1096 = fresh_x_a "x" a  in
                               [uu____1096]  in
                             FStar_List.append rest_bs uu____1087  in
                           a :: uu____1078  in
                         let uu____1128 =
                           let uu____1133 =
                             FStar_TypeChecker_Env.push_binders env bs  in
                           let uu____1134 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.fst a)
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           fresh_repr r uu____1133 u_a uu____1134  in
                         (match uu____1128 with
                          | (repr1,g) ->
                              let k =
                                let uu____1154 =
                                  FStar_Syntax_Syntax.mk_Total' repr1
                                    (FStar_Pervasives_Native.Some u_a)
                                   in
                                FStar_Syntax_Util.arrow bs uu____1154  in
                              let g_eq = FStar_TypeChecker_Rel.teq env ty k
                                 in
                              ((let uu____1159 =
                                  FStar_TypeChecker_Env.conj_guard g g_eq  in
                                FStar_TypeChecker_Rel.force_trivial_guard env
                                  uu____1159);
                               (let uu____1160 =
                                  let uu____1163 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env k
                                     in
                                  FStar_Syntax_Subst.close_univ_vars us
                                    uu____1163
                                   in
                                (ret_us, ret_t, uu____1160))))))
            in
         log_combinator "return_repr" return_repr;
         (let bind_repr =
            let r =
              (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
               in
            let uu____1190 =
              check_and_gen' "bind_repr" (Prims.of_int (2))
                FStar_Pervasives_Native.None ed.FStar_Syntax_Syntax.bind_repr
               in
            match uu____1190 with
            | (bind_us,bind_t,bind_ty) ->
                let uu____1214 =
                  FStar_Syntax_Subst.open_univ_vars bind_us bind_ty  in
                (match uu____1214 with
                 | (us,ty) ->
                     let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                        in
                     let uu____1234 = fresh_a_and_u_a "a"  in
                     (match uu____1234 with
                      | (a,u_a) ->
                          let uu____1254 = fresh_a_and_u_a "b"  in
                          (match uu____1254 with
                           | (b,u_b) ->
                               let rest_bs =
                                 let uu____1283 =
                                   let uu____1284 =
                                     FStar_Syntax_Subst.compress ty  in
                                   uu____1284.FStar_Syntax_Syntax.n  in
                                 match uu____1283 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____1296) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (4))
                                     ->
                                     let uu____1324 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____1324 with
                                      | (a',uu____1334)::(b',uu____1336)::bs1
                                          ->
                                          let uu____1366 =
                                            FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 (Prims.of_int (2))) bs1
                                             in
                                          (match uu____1366 with
                                           | (bs2,uu____1409) ->
                                               let substs =
                                                 let uu____1445 =
                                                   let uu____1446 =
                                                     let uu____1453 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a', uu____1453)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____1446
                                                    in
                                                 let uu____1460 =
                                                   let uu____1463 =
                                                     let uu____1464 =
                                                       let uu____1471 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              b)
                                                          in
                                                       (b', uu____1471)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____1464
                                                      in
                                                   [uu____1463]  in
                                                 uu____1445 :: uu____1460  in
                                               FStar_Syntax_Subst.subst_binders
                                                 substs bs2)
                                      | uu____1478 -> failwith "Impossible!")
                                 | uu____1488 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_UnexpectedEffect,
                                         "") r
                                  in
                               let bs = a :: b :: rest_bs  in
                               let uu____1520 =
                                 let uu____1531 =
                                   let uu____1536 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____1537 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____1536 u_a uu____1537  in
                                 match uu____1531 with
                                 | (repr1,g) ->
                                     let uu____1552 =
                                       let uu____1559 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None repr1
                                          in
                                       FStar_All.pipe_right uu____1559
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____1552, g)
                                  in
                               (match uu____1520 with
                                | (f,g_f) ->
                                    let uu____1599 =
                                      let x_a = fresh_x_a "x" a  in
                                      let uu____1612 =
                                        let uu____1617 =
                                          FStar_TypeChecker_Env.push_binders
                                            env (FStar_List.append bs [x_a])
                                           in
                                        let uu____1636 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst b)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____1617 u_b
                                          uu____1636
                                         in
                                      match uu____1612 with
                                      | (repr1,g) ->
                                          let uu____1651 =
                                            let uu____1658 =
                                              let uu____1659 =
                                                let uu____1660 =
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1
                                                    (FStar_Pervasives_Native.Some
                                                       u_b)
                                                   in
                                                FStar_Syntax_Util.arrow 
                                                  [x_a] uu____1660
                                                 in
                                              FStar_Syntax_Syntax.gen_bv "g"
                                                FStar_Pervasives_Native.None
                                                uu____1659
                                               in
                                            FStar_All.pipe_right uu____1658
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____1651, g)
                                       in
                                    (match uu____1599 with
                                     | (g,g_g) ->
                                         let uu____1714 =
                                           let uu____1719 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____1720 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst b)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____1719 u_b
                                             uu____1720
                                            in
                                         (match uu____1714 with
                                          | (repr1,g_repr) ->
                                              let k =
                                                let uu____1740 =
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1
                                                    (FStar_Pervasives_Native.Some
                                                       u_b)
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  (FStar_List.append bs
                                                     [f; g]) uu____1740
                                                 in
                                              let g_eq =
                                                FStar_TypeChecker_Rel.teq env
                                                  ty k
                                                 in
                                              (FStar_List.iter
                                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                                    env)
                                                 [g_f; g_g; g_repr; g_eq];
                                               (let uu____1769 =
                                                  let uu____1772 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Beta]
                                                      env k
                                                     in
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    bind_us uu____1772
                                                   in
                                                (bind_us, bind_t, uu____1769)))))))))
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
             let uu____1814 =
               check_and_gen' "stronger_repr" Prims.int_one
                 FStar_Pervasives_Native.None stronger_repr
                in
             match uu____1814 with
             | (stronger_us,stronger_t,stronger_ty) ->
                 ((let uu____1839 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                       (FStar_Options.Other "LayeredEffects")
                      in
                   if uu____1839
                   then
                     let uu____1844 =
                       FStar_Syntax_Print.tscheme_to_string
                         (stronger_us, stronger_t)
                        in
                     let uu____1850 =
                       FStar_Syntax_Print.tscheme_to_string
                         (stronger_us, stronger_ty)
                        in
                     FStar_Util.print2
                       "stronger combinator typechecked with term: %s and type: %s\n"
                       uu____1844 uu____1850
                   else ());
                  (let uu____1859 =
                     FStar_Syntax_Subst.open_univ_vars stronger_us
                       stronger_ty
                      in
                   match uu____1859 with
                   | (us,ty) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                          in
                       let uu____1879 = fresh_a_and_u_a "a"  in
                       (match uu____1879 with
                        | (a,u) ->
                            let rest_bs =
                              let uu____1908 =
                                let uu____1909 =
                                  FStar_Syntax_Subst.compress ty  in
                                uu____1909.FStar_Syntax_Syntax.n  in
                              match uu____1908 with
                              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1921)
                                  when
                                  (FStar_List.length bs) >=
                                    (Prims.of_int (2))
                                  ->
                                  let uu____1949 =
                                    FStar_Syntax_Subst.open_binders bs  in
                                  (match uu____1949 with
                                   | (a',uu____1959)::bs1 ->
                                       let uu____1979 =
                                         FStar_List.splitAt
                                           ((FStar_List.length bs1) -
                                              Prims.int_one) bs1
                                          in
                                       (match uu____1979 with
                                        | (bs2,uu____2022) ->
                                            let substs =
                                              let uu____2058 =
                                                let uu____2059 =
                                                  let uu____2066 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____2066)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____2059
                                                 in
                                              [uu____2058]  in
                                            FStar_Syntax_Subst.subst_binders
                                              substs bs2)
                                   | uu____2073 -> failwith "Impossible!")
                              | uu____2083 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnexpectedEffect, "")
                                    r
                               in
                            let bs = a :: rest_bs  in
                            let uu____2109 =
                              let uu____2120 =
                                let uu____2125 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                let uu____2126 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.fst a)
                                    FStar_Syntax_Syntax.bv_to_name
                                   in
                                fresh_repr r uu____2125 u uu____2126  in
                              match uu____2120 with
                              | (repr1,g) ->
                                  let uu____2141 =
                                    let uu____2148 =
                                      FStar_Syntax_Syntax.gen_bv "f"
                                        FStar_Pervasives_Native.None repr1
                                       in
                                    FStar_All.pipe_right uu____2148
                                      FStar_Syntax_Syntax.mk_binder
                                     in
                                  (uu____2141, g)
                               in
                            (match uu____2109 with
                             | (f,g_f) ->
                                 let uu____2188 =
                                   let uu____2193 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____2194 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____2193 u uu____2194  in
                                 (match uu____2188 with
                                  | (ret_t,g_ret_t) ->
                                      let pure_wp_t =
                                        let pure_wp_ts =
                                          let uu____2213 =
                                            FStar_TypeChecker_Env.lookup_definition
                                              [FStar_TypeChecker_Env.NoDelta]
                                              env
                                              FStar_Parser_Const.pure_wp_lid
                                             in
                                          FStar_All.pipe_right uu____2213
                                            FStar_Util.must
                                           in
                                        let uu____2218 =
                                          FStar_TypeChecker_Env.inst_tscheme
                                            pure_wp_ts
                                           in
                                        match uu____2218 with
                                        | (uu____2223,pure_wp_t) ->
                                            let uu____2225 =
                                              let uu____2230 =
                                                let uu____2231 =
                                                  FStar_All.pipe_right ret_t
                                                    FStar_Syntax_Syntax.as_arg
                                                   in
                                                [uu____2231]  in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                pure_wp_t uu____2230
                                               in
                                            uu____2225
                                              FStar_Pervasives_Native.None r
                                         in
                                      let uu____2264 =
                                        let uu____2277 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" r uu____2277 pure_wp_t
                                         in
                                      (match uu____2264 with
                                       | (pure_wp_uvar,uu____2292,g_pure_wp_uvar)
                                           ->
                                           let c =
                                             let uu____2307 =
                                               let uu____2308 =
                                                 let uu____2309 =
                                                   FStar_TypeChecker_Env.new_u_univ
                                                     ()
                                                    in
                                                 [uu____2309]  in
                                               let uu____2310 =
                                                 let uu____2321 =
                                                   FStar_All.pipe_right
                                                     pure_wp_uvar
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 [uu____2321]  in
                                               {
                                                 FStar_Syntax_Syntax.comp_univs
                                                   = uu____2308;
                                                 FStar_Syntax_Syntax.effect_name
                                                   =
                                                   FStar_Parser_Const.effect_PURE_lid;
                                                 FStar_Syntax_Syntax.result_typ
                                                   = ret_t;
                                                 FStar_Syntax_Syntax.effect_args
                                                   = uu____2310;
                                                 FStar_Syntax_Syntax.flags =
                                                   []
                                               }  in
                                             FStar_Syntax_Syntax.mk_Comp
                                               uu____2307
                                              in
                                           let k =
                                             FStar_Syntax_Util.arrow
                                               (FStar_List.append bs [f]) c
                                              in
                                           ((let uu____2376 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____2376
                                             then
                                               let uu____2381 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected type before unification: %s\n"
                                                 uu____2381
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env
                                                 ty k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env)
                                               [g_f; g_ret_t; g_pure_wp_uvar];
                                             (let k1 =
                                                FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                  env k
                                                 in
                                              let uu____2389 =
                                                let uu____2392 =
                                                  FStar_All.pipe_right k1
                                                    (FStar_TypeChecker_Normalize.normalize
                                                       [FStar_TypeChecker_Env.Beta;
                                                       FStar_TypeChecker_Env.Eager_unfolding]
                                                       env)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2392
                                                  (FStar_Syntax_Subst.close_univ_vars
                                                     stronger_us)
                                                 in
                                              (stronger_us, stronger_t,
                                                uu____2389))))))))))
              in
           log_combinator "stronger_repr" stronger_repr;
           (let tc_action env act =
              let r =
                (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                 in
              if
                (FStar_List.length act.FStar_Syntax_Syntax.action_params) <>
                  Prims.int_zero
              then
                failwith
                  "tc_layered_eff_decl: expected action_params to be empty"
              else ();
              (let uu____2428 =
                 let uu____2433 =
                   FStar_Syntax_Subst.univ_var_opening
                     act.FStar_Syntax_Syntax.action_univs
                    in
                 match uu____2433 with
                 | (usubst,us) ->
                     let uu____2456 =
                       FStar_TypeChecker_Env.push_univ_vars env us  in
                     let uu____2457 =
                       let uu___278_2458 = act  in
                       let uu____2459 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_defn
                          in
                       let uu____2460 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_typ
                          in
                       {
                         FStar_Syntax_Syntax.action_name =
                           (uu___278_2458.FStar_Syntax_Syntax.action_name);
                         FStar_Syntax_Syntax.action_unqualified_name =
                           (uu___278_2458.FStar_Syntax_Syntax.action_unqualified_name);
                         FStar_Syntax_Syntax.action_univs = us;
                         FStar_Syntax_Syntax.action_params =
                           (uu___278_2458.FStar_Syntax_Syntax.action_params);
                         FStar_Syntax_Syntax.action_defn = uu____2459;
                         FStar_Syntax_Syntax.action_typ = uu____2460
                       }  in
                     (uu____2456, uu____2457)
                  in
               match uu____2428 with
               | (env1,act1) ->
                   let act_typ =
                     let uu____2464 =
                       let uu____2465 =
                         FStar_Syntax_Subst.compress
                           act1.FStar_Syntax_Syntax.action_typ
                          in
                       uu____2465.FStar_Syntax_Syntax.n  in
                     match uu____2464 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                         let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
                         let uu____2491 =
                           FStar_Ident.lid_equals
                             ct.FStar_Syntax_Syntax.effect_name
                             ed.FStar_Syntax_Syntax.mname
                            in
                         if uu____2491
                         then
                           let repr_ts =
                             let uu____2495 = repr  in
                             match uu____2495 with
                             | (us,t,uu____2510) -> (us, t)  in
                           let repr1 =
                             let uu____2528 =
                               FStar_TypeChecker_Env.inst_tscheme_with
                                 repr_ts ct.FStar_Syntax_Syntax.comp_univs
                                in
                             FStar_All.pipe_right uu____2528
                               FStar_Pervasives_Native.snd
                              in
                           let c1 =
                             let uu____2540 =
                               let uu____2541 =
                                 let uu____2546 =
                                   let uu____2547 =
                                     FStar_Syntax_Syntax.as_arg
                                       ct.FStar_Syntax_Syntax.result_typ
                                      in
                                   uu____2547 ::
                                     (ct.FStar_Syntax_Syntax.effect_args)
                                    in
                                 FStar_Syntax_Syntax.mk_Tm_app repr1
                                   uu____2546
                                  in
                               uu____2541 FStar_Pervasives_Native.None r  in
                             FStar_All.pipe_right uu____2540
                               FStar_Syntax_Syntax.mk_Total
                              in
                           FStar_Syntax_Util.arrow bs c1
                         else act1.FStar_Syntax_Syntax.action_typ
                     | uu____2568 -> act1.FStar_Syntax_Syntax.action_typ  in
                   let uu____2569 =
                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                       act_typ
                      in
                   (match uu____2569 with
                    | (act_typ1,uu____2577,g_t) ->
                        let uu____2579 =
                          let uu____2586 =
                            let uu___302_2587 =
                              FStar_TypeChecker_Env.set_expected_typ env1
                                act_typ1
                               in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___302_2587.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___302_2587.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___302_2587.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___302_2587.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___302_2587.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___302_2587.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___302_2587.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___302_2587.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___302_2587.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___302_2587.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___302_2587.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp = false;
                              FStar_TypeChecker_Env.effects =
                                (uu___302_2587.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___302_2587.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___302_2587.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___302_2587.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___302_2587.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___302_2587.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___302_2587.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___302_2587.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax =
                                (uu___302_2587.FStar_TypeChecker_Env.lax);
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___302_2587.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___302_2587.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___302_2587.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___302_2587.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___302_2587.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___302_2587.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___302_2587.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___302_2587.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___302_2587.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___302_2587.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___302_2587.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___302_2587.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___302_2587.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___302_2587.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___302_2587.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___302_2587.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___302_2587.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___302_2587.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___302_2587.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___302_2587.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___302_2587.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___302_2587.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___302_2587.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___302_2587.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                            uu____2586 act1.FStar_Syntax_Syntax.action_defn
                           in
                        (match uu____2579 with
                         | (act_defn,uu____2590,g_d) ->
                             ((let uu____2593 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env1)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____2593
                               then
                                 let uu____2598 =
                                   FStar_Syntax_Print.term_to_string act_defn
                                    in
                                 let uu____2600 =
                                   FStar_Syntax_Print.term_to_string act_typ1
                                    in
                                 FStar_Util.print2
                                   "Typechecked action definition: %s and action type: %s\n"
                                   uu____2598 uu____2600
                               else ());
                              (let uu____2605 =
                                 let act_typ2 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Beta] env1
                                     act_typ1
                                    in
                                 let uu____2613 =
                                   let uu____2614 =
                                     FStar_Syntax_Subst.compress act_typ2  in
                                   uu____2614.FStar_Syntax_Syntax.n  in
                                 match uu____2613 with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                     let bs1 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     let env2 =
                                       FStar_TypeChecker_Env.push_binders
                                         env1 bs1
                                        in
                                     let uu____2647 =
                                       FStar_Syntax_Util.type_u ()  in
                                     (match uu____2647 with
                                      | (t,u) ->
                                          let uu____2660 =
                                            FStar_TypeChecker_Util.new_implicit_var
                                              "" r env2 t
                                             in
                                          (match uu____2660 with
                                           | (a_tm,uu____2681,g_tm) ->
                                               let uu____2695 =
                                                 fresh_repr r env2 u a_tm  in
                                               (match uu____2695 with
                                                | (repr1,g) ->
                                                    let uu____2708 =
                                                      let uu____2711 =
                                                        let uu____2714 =
                                                          let uu____2717 =
                                                            FStar_TypeChecker_Env.new_u_univ
                                                              ()
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2717
                                                            (fun _2720  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _2720)
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total'
                                                          repr1 uu____2714
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____2711
                                                       in
                                                    let uu____2721 =
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g g_tm
                                                       in
                                                    (uu____2708, uu____2721))))
                                 | uu____2724 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                         "") r
                                  in
                               match uu____2605 with
                               | (k,g_k) ->
                                   ((let uu____2740 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other
                                            "LayeredEffects")
                                        in
                                     if uu____2740
                                     then
                                       let uu____2745 =
                                         FStar_Syntax_Print.term_to_string k
                                          in
                                       FStar_Util.print1
                                         "Expected action type: %s\n"
                                         uu____2745
                                     else ());
                                    (let g =
                                       FStar_TypeChecker_Rel.teq env1
                                         act_typ1 k
                                        in
                                     FStar_List.iter
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1) [g_t; g_d; g_k; g];
                                     (let uu____2753 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____2753
                                      then
                                        let uu____2758 =
                                          FStar_Syntax_Print.term_to_string k
                                           in
                                        FStar_Util.print1
                                          "Expected action type after unification: %s\n"
                                          uu____2758
                                      else ());
                                     (let act_typ2 =
                                        let repr_args t =
                                          let uu____2782 =
                                            let uu____2783 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____2783.FStar_Syntax_Syntax.n
                                             in
                                          match uu____2782 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (head1,a::is) ->
                                              let uu____2835 =
                                                let uu____2836 =
                                                  FStar_Syntax_Subst.compress
                                                    head1
                                                   in
                                                uu____2836.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____2835 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (uu____2845,us) ->
                                                   (us,
                                                     (FStar_Pervasives_Native.fst
                                                        a), is)
                                               | uu____2855 ->
                                                   failwith "Impossible!")
                                          | uu____2863 ->
                                              failwith "Impossible!"
                                           in
                                        let k1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Env.Beta] env1
                                            k
                                           in
                                        let uu____2872 =
                                          let uu____2873 =
                                            FStar_Syntax_Subst.compress k1
                                             in
                                          uu____2873.FStar_Syntax_Syntax.n
                                           in
                                        match uu____2872 with
                                        | FStar_Syntax_Syntax.Tm_arrow 
                                            (bs,c) ->
                                            let uu____2898 =
                                              FStar_Syntax_Subst.open_comp bs
                                                c
                                               in
                                            (match uu____2898 with
                                             | (bs1,c1) ->
                                                 let uu____2905 =
                                                   repr_args
                                                     (FStar_Syntax_Util.comp_result
                                                        c1)
                                                    in
                                                 (match uu____2905 with
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
                                                      let uu____2916 =
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          ct
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____2916))
                                        | uu____2919 ->
                                            failwith "Impossible!"
                                         in
                                      (let uu____2922 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____2922
                                       then
                                         let uu____2927 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ2
                                            in
                                         FStar_Util.print1
                                           "Action type after injecting it into the monad: %s\n"
                                           uu____2927
                                       else ());
                                      (let act2 =
                                         if
                                           act1.FStar_Syntax_Syntax.action_univs
                                             = []
                                         then
                                           let uu____2936 =
                                             FStar_TypeChecker_Util.generalize_universes
                                               env1 act_defn
                                              in
                                           match uu____2936 with
                                           | (us,act_defn1) ->
                                               let uu___372_2947 = act1  in
                                               let uu____2948 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   us act_typ2
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___372_2947.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___372_2947.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = us;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___372_2947.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = act_defn1;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = uu____2948
                                               }
                                         else
                                           (let uu___374_2951 = act1  in
                                            let uu____2952 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                act1.FStar_Syntax_Syntax.action_univs
                                                act_defn
                                               in
                                            let uu____2953 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                act1.FStar_Syntax_Syntax.action_univs
                                                act_typ2
                                               in
                                            {
                                              FStar_Syntax_Syntax.action_name
                                                =
                                                (uu___374_2951.FStar_Syntax_Syntax.action_name);
                                              FStar_Syntax_Syntax.action_unqualified_name
                                                =
                                                (uu___374_2951.FStar_Syntax_Syntax.action_unqualified_name);
                                              FStar_Syntax_Syntax.action_univs
                                                =
                                                (uu___374_2951.FStar_Syntax_Syntax.action_univs);
                                              FStar_Syntax_Syntax.action_params
                                                =
                                                (uu___374_2951.FStar_Syntax_Syntax.action_params);
                                              FStar_Syntax_Syntax.action_defn
                                                = uu____2952;
                                              FStar_Syntax_Syntax.action_typ
                                                = uu____2953
                                            })
                                          in
                                       act2)))))))))
               in
            let fst1 uu____2973 =
              match uu____2973 with | (a,uu____2989,uu____2990) -> a  in
            let snd1 uu____3022 =
              match uu____3022 with | (uu____3037,b,uu____3039) -> b  in
            let thd uu____3071 =
              match uu____3071 with | (uu____3086,uu____3087,c) -> c  in
            let uu___392_3101 = ed  in
            let uu____3102 =
              FStar_All.pipe_right
                ((fst1 stronger_repr), (snd1 stronger_repr))
                (fun _3111  -> FStar_Pervasives_Native.Some _3111)
               in
            let uu____3112 =
              FStar_List.map (tc_action env0) ed.FStar_Syntax_Syntax.actions
               in
            {
              FStar_Syntax_Syntax.is_layered =
                (uu___392_3101.FStar_Syntax_Syntax.is_layered);
              FStar_Syntax_Syntax.cattributes =
                (uu___392_3101.FStar_Syntax_Syntax.cattributes);
              FStar_Syntax_Syntax.mname =
                (uu___392_3101.FStar_Syntax_Syntax.mname);
              FStar_Syntax_Syntax.univs =
                (uu___392_3101.FStar_Syntax_Syntax.univs);
              FStar_Syntax_Syntax.binders =
                (uu___392_3101.FStar_Syntax_Syntax.binders);
              FStar_Syntax_Syntax.signature =
                ((fst1 signature), (snd1 signature));
              FStar_Syntax_Syntax.ret_wp =
                ((fst1 return_repr), (thd return_repr));
              FStar_Syntax_Syntax.bind_wp =
                ((fst1 bind_repr), (thd bind_repr));
              FStar_Syntax_Syntax.stronger =
                ((fst1 stronger_repr), (thd stronger_repr));
              FStar_Syntax_Syntax.match_wps =
                (uu___392_3101.FStar_Syntax_Syntax.match_wps);
              FStar_Syntax_Syntax.trivial =
                (uu___392_3101.FStar_Syntax_Syntax.trivial);
              FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
              FStar_Syntax_Syntax.return_repr =
                ((fst1 return_repr), (snd1 return_repr));
              FStar_Syntax_Syntax.bind_repr =
                ((fst1 bind_repr), (snd1 bind_repr));
              FStar_Syntax_Syntax.stronger_repr = uu____3102;
              FStar_Syntax_Syntax.actions = uu____3112;
              FStar_Syntax_Syntax.eff_attrs =
                (uu___392_3101.FStar_Syntax_Syntax.eff_attrs)
            }))))))
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____3159 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____3159 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____3186 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____3186
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____3199 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "ED")
          in
       if uu____3199
       then
         let uu____3204 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____3204
       else ());
      (let uu____3210 =
         let uu____3215 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____3215 with
         | (ed_univs_subst,ed_univs) ->
             let bs =
               let uu____3239 =
                 FStar_Syntax_Subst.subst_binders ed_univs_subst
                   ed.FStar_Syntax_Syntax.binders
                  in
               FStar_Syntax_Subst.open_binders uu____3239  in
             let uu____3240 =
               let uu____3247 =
                 FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
               FStar_TypeChecker_TcTerm.tc_tparams uu____3247 bs  in
             (match uu____3240 with
              | (bs1,uu____3253,uu____3254) ->
                  let uu____3255 =
                    let tmp_t =
                      let uu____3265 =
                        let uu____3268 =
                          FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                            (fun _3273  -> FStar_Pervasives_Native.Some _3273)
                           in
                        FStar_Syntax_Syntax.mk_Total'
                          FStar_Syntax_Syntax.t_unit uu____3268
                         in
                      FStar_Syntax_Util.arrow bs1 uu____3265  in
                    let uu____3274 =
                      FStar_TypeChecker_Util.generalize_universes env0 tmp_t
                       in
                    match uu____3274 with
                    | (us,tmp_t1) ->
                        let uu____3291 =
                          let uu____3292 =
                            let uu____3293 =
                              FStar_All.pipe_right tmp_t1
                                FStar_Syntax_Util.arrow_formals
                               in
                            FStar_All.pipe_right uu____3293
                              FStar_Pervasives_Native.fst
                             in
                          FStar_All.pipe_right uu____3292
                            FStar_Syntax_Subst.close_binders
                           in
                        (us, uu____3291)
                     in
                  (match uu____3255 with
                   | (us,bs2) ->
                       (match ed_univs with
                        | [] -> (us, bs2)
                        | uu____3362 ->
                            let uu____3365 =
                              ((FStar_List.length ed_univs) =
                                 (FStar_List.length us))
                                &&
                                (FStar_List.forall2
                                   (fun u1  ->
                                      fun u2  ->
                                        let uu____3372 =
                                          FStar_Syntax_Syntax.order_univ_name
                                            u1 u2
                                           in
                                        uu____3372 = Prims.int_zero) ed_univs
                                   us)
                               in
                            if uu____3365
                            then (us, bs2)
                            else
                              (let uu____3383 =
                                 let uu____3389 =
                                   let uu____3391 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length ed_univs)
                                      in
                                   let uu____3393 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length us)
                                      in
                                   FStar_Util.format3
                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                     uu____3391 uu____3393
                                    in
                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                   uu____3389)
                                  in
                               let uu____3397 =
                                 FStar_Ident.range_of_lid
                                   ed.FStar_Syntax_Syntax.mname
                                  in
                               FStar_Errors.raise_error uu____3383 uu____3397))))
          in
       match uu____3210 with
       | (us,bs) ->
           let ed1 =
             let uu___432_3405 = ed  in
             {
               FStar_Syntax_Syntax.is_layered =
                 (uu___432_3405.FStar_Syntax_Syntax.is_layered);
               FStar_Syntax_Syntax.cattributes =
                 (uu___432_3405.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___432_3405.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs = us;
               FStar_Syntax_Syntax.binders = bs;
               FStar_Syntax_Syntax.signature =
                 (uu___432_3405.FStar_Syntax_Syntax.signature);
               FStar_Syntax_Syntax.ret_wp =
                 (uu___432_3405.FStar_Syntax_Syntax.ret_wp);
               FStar_Syntax_Syntax.bind_wp =
                 (uu___432_3405.FStar_Syntax_Syntax.bind_wp);
               FStar_Syntax_Syntax.stronger =
                 (uu___432_3405.FStar_Syntax_Syntax.stronger);
               FStar_Syntax_Syntax.match_wps =
                 (uu___432_3405.FStar_Syntax_Syntax.match_wps);
               FStar_Syntax_Syntax.trivial =
                 (uu___432_3405.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr =
                 (uu___432_3405.FStar_Syntax_Syntax.repr);
               FStar_Syntax_Syntax.return_repr =
                 (uu___432_3405.FStar_Syntax_Syntax.return_repr);
               FStar_Syntax_Syntax.bind_repr =
                 (uu___432_3405.FStar_Syntax_Syntax.bind_repr);
               FStar_Syntax_Syntax.stronger_repr =
                 (uu___432_3405.FStar_Syntax_Syntax.stronger_repr);
               FStar_Syntax_Syntax.actions =
                 (uu___432_3405.FStar_Syntax_Syntax.actions);
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___432_3405.FStar_Syntax_Syntax.eff_attrs)
             }  in
           let uu____3406 = FStar_Syntax_Subst.univ_var_opening us  in
           (match uu____3406 with
            | (ed_univs_subst,ed_univs) ->
                let uu____3425 =
                  let uu____3430 =
                    FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                  FStar_Syntax_Subst.open_binders' uu____3430  in
                (match uu____3425 with
                 | (ed_bs,ed_bs_subst) ->
                     let ed2 =
                       let op uu____3451 =
                         match uu____3451 with
                         | (us1,t) ->
                             let t1 =
                               let uu____3471 =
                                 FStar_Syntax_Subst.shift_subst
                                   ((FStar_List.length ed_bs) +
                                      (FStar_List.length us1)) ed_univs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____3471 t  in
                             let uu____3480 =
                               let uu____3481 =
                                 FStar_Syntax_Subst.shift_subst
                                   (FStar_List.length us1) ed_bs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____3481 t1  in
                             (us1, uu____3480)
                          in
                       let uu___446_3486 = ed1  in
                       let uu____3487 = op ed1.FStar_Syntax_Syntax.signature
                          in
                       let uu____3488 = op ed1.FStar_Syntax_Syntax.ret_wp  in
                       let uu____3489 = op ed1.FStar_Syntax_Syntax.bind_wp
                          in
                       let uu____3490 = op ed1.FStar_Syntax_Syntax.stronger
                          in
                       let uu____3491 =
                         FStar_Syntax_Util.map_match_wps op
                           ed1.FStar_Syntax_Syntax.match_wps
                          in
                       let uu____3496 =
                         FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                           op
                          in
                       let uu____3499 = op ed1.FStar_Syntax_Syntax.repr  in
                       let uu____3500 =
                         op ed1.FStar_Syntax_Syntax.return_repr  in
                       let uu____3501 = op ed1.FStar_Syntax_Syntax.bind_repr
                          in
                       let uu____3502 =
                         FStar_List.map
                           (fun a  ->
                              let uu___449_3510 = a  in
                              let uu____3511 =
                                let uu____3512 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____3512  in
                              let uu____3523 =
                                let uu____3524 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_typ))
                                   in
                                FStar_Pervasives_Native.snd uu____3524  in
                              {
                                FStar_Syntax_Syntax.action_name =
                                  (uu___449_3510.FStar_Syntax_Syntax.action_name);
                                FStar_Syntax_Syntax.action_unqualified_name =
                                  (uu___449_3510.FStar_Syntax_Syntax.action_unqualified_name);
                                FStar_Syntax_Syntax.action_univs =
                                  (uu___449_3510.FStar_Syntax_Syntax.action_univs);
                                FStar_Syntax_Syntax.action_params =
                                  (uu___449_3510.FStar_Syntax_Syntax.action_params);
                                FStar_Syntax_Syntax.action_defn = uu____3511;
                                FStar_Syntax_Syntax.action_typ = uu____3523
                              }) ed1.FStar_Syntax_Syntax.actions
                          in
                       {
                         FStar_Syntax_Syntax.is_layered =
                           (uu___446_3486.FStar_Syntax_Syntax.is_layered);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___446_3486.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___446_3486.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___446_3486.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___446_3486.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature = uu____3487;
                         FStar_Syntax_Syntax.ret_wp = uu____3488;
                         FStar_Syntax_Syntax.bind_wp = uu____3489;
                         FStar_Syntax_Syntax.stronger = uu____3490;
                         FStar_Syntax_Syntax.match_wps = uu____3491;
                         FStar_Syntax_Syntax.trivial = uu____3496;
                         FStar_Syntax_Syntax.repr = uu____3499;
                         FStar_Syntax_Syntax.return_repr = uu____3500;
                         FStar_Syntax_Syntax.bind_repr = uu____3501;
                         FStar_Syntax_Syntax.stronger_repr =
                           FStar_Pervasives_Native.None;
                         FStar_Syntax_Syntax.actions = uu____3502;
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___446_3486.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     ((let uu____3536 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "ED")
                          in
                       if uu____3536
                       then
                         let uu____3541 =
                           FStar_Syntax_Print.eff_decl_to_string false ed2
                            in
                         FStar_Util.print1
                           "After typechecking binders eff_decl: \n\t%s\n"
                           uu____3541
                       else ());
                      (let env =
                         let uu____3548 =
                           FStar_TypeChecker_Env.push_univ_vars env0 ed_univs
                            in
                         FStar_TypeChecker_Env.push_binders uu____3548 ed_bs
                          in
                       let check_and_gen' comb n1 env_opt uu____3583 k =
                         match uu____3583 with
                         | (us1,t) ->
                             let env1 =
                               if FStar_Util.is_some env_opt
                               then
                                 FStar_All.pipe_right env_opt FStar_Util.must
                               else env  in
                             let uu____3603 =
                               FStar_Syntax_Subst.open_univ_vars us1 t  in
                             (match uu____3603 with
                              | (us2,t1) ->
                                  let t2 =
                                    match k with
                                    | FStar_Pervasives_Native.Some k1 ->
                                        let uu____3612 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 us2
                                           in
                                        tc_check_trivial_guard uu____3612 t1
                                          k1
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____3613 =
                                          let uu____3620 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            uu____3620 t1
                                           in
                                        (match uu____3613 with
                                         | (t2,uu____3622,g) ->
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env1 g;
                                              t2))
                                     in
                                  let uu____3625 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env1 t2
                                     in
                                  (match uu____3625 with
                                   | (g_us,t3) ->
                                       (if (FStar_List.length g_us) <> n1
                                        then
                                          (let error =
                                             let uu____3641 =
                                               FStar_Util.string_of_int n1
                                                in
                                             let uu____3643 =
                                               let uu____3645 =
                                                 FStar_All.pipe_right g_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3645
                                                 FStar_Util.string_of_int
                                                in
                                             FStar_Util.format4
                                               "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                               (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               comb uu____3641 uu____3643
                                              in
                                           FStar_Errors.raise_error
                                             (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                               error)
                                             t3.FStar_Syntax_Syntax.pos)
                                        else ();
                                        (match us2 with
                                         | [] -> (g_us, t3)
                                         | uu____3660 ->
                                             let uu____3661 =
                                               ((FStar_List.length us2) =
                                                  (FStar_List.length g_us))
                                                 &&
                                                 (FStar_List.forall2
                                                    (fun u1  ->
                                                       fun u2  ->
                                                         let uu____3668 =
                                                           FStar_Syntax_Syntax.order_univ_name
                                                             u1 u2
                                                            in
                                                         uu____3668 =
                                                           Prims.int_zero)
                                                    us2 g_us)
                                                in
                                             if uu____3661
                                             then (g_us, t3)
                                             else
                                               (let uu____3679 =
                                                  let uu____3685 =
                                                    let uu____3687 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           us2)
                                                       in
                                                    let uu____3689 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           g_us)
                                                       in
                                                    FStar_Util.format4
                                                      "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                      (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      comb uu____3687
                                                      uu____3689
                                                     in
                                                  (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                    uu____3685)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____3679
                                                  t3.FStar_Syntax_Syntax.pos)))))
                          in
                       let signature =
                         check_and_gen' "signature" Prims.int_one
                           FStar_Pervasives_Native.None
                           ed2.FStar_Syntax_Syntax.signature
                           FStar_Pervasives_Native.None
                          in
                       (let uu____3697 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "ED")
                           in
                        if uu____3697
                        then
                          let uu____3702 =
                            FStar_Syntax_Print.tscheme_to_string signature
                             in
                          FStar_Util.print1 "Typechecked signature: %s\n"
                            uu____3702
                        else ());
                       (let fresh_a_and_wp uu____3718 =
                          let fail1 t =
                            let uu____3731 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env ed2.FStar_Syntax_Syntax.mname t
                               in
                            FStar_Errors.raise_error uu____3731
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                             in
                          let uu____3747 =
                            FStar_TypeChecker_Env.inst_tscheme signature  in
                          match uu____3747 with
                          | (uu____3758,signature1) ->
                              let uu____3760 =
                                let uu____3761 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____3761.FStar_Syntax_Syntax.n  in
                              (match uu____3760 with
                               | FStar_Syntax_Syntax.Tm_arrow
                                   (bs1,uu____3771) ->
                                   let bs2 =
                                     FStar_Syntax_Subst.open_binders bs1  in
                                   (match bs2 with
                                    | (a,uu____3800)::(wp,uu____3802)::[] ->
                                        (a, (wp.FStar_Syntax_Syntax.sort))
                                    | uu____3831 -> fail1 signature1)
                               | uu____3832 -> fail1 signature1)
                           in
                        let log_combinator s ts =
                          let uu____3846 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ED")
                             in
                          if uu____3846
                          then
                            let uu____3851 =
                              FStar_Syntax_Print.tscheme_to_string ts  in
                            FStar_Util.print3 "Typechecked %s:%s = %s\n"
                              (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                              s uu____3851
                          else ()  in
                        let ret_wp =
                          let uu____3857 = fresh_a_and_wp ()  in
                          match uu____3857 with
                          | (a,wp_sort) ->
                              let k =
                                let uu____3873 =
                                  let uu____3882 =
                                    FStar_Syntax_Syntax.mk_binder a  in
                                  let uu____3889 =
                                    let uu____3898 =
                                      let uu____3905 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____3905
                                       in
                                    [uu____3898]  in
                                  uu____3882 :: uu____3889  in
                                let uu____3924 =
                                  FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                FStar_Syntax_Util.arrow uu____3873 uu____3924
                                 in
                              check_and_gen' "ret_wp" Prims.int_one
                                FStar_Pervasives_Native.None
                                ed2.FStar_Syntax_Syntax.ret_wp
                                (FStar_Pervasives_Native.Some k)
                           in
                        log_combinator "ret_wp" ret_wp;
                        (let bind_wp =
                           let uu____3932 = fresh_a_and_wp ()  in
                           match uu____3932 with
                           | (a,wp_sort_a) ->
                               let uu____3945 = fresh_a_and_wp ()  in
                               (match uu____3945 with
                                | (b,wp_sort_b) ->
                                    let wp_sort_a_b =
                                      let uu____3961 =
                                        let uu____3970 =
                                          let uu____3977 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____3977
                                           in
                                        [uu____3970]  in
                                      let uu____3990 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____3961
                                        uu____3990
                                       in
                                    let k =
                                      let uu____3996 =
                                        let uu____4005 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____4012 =
                                          let uu____4021 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4028 =
                                            let uu____4037 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4044 =
                                              let uu____4053 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              let uu____4060 =
                                                let uu____4069 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a_b
                                                   in
                                                [uu____4069]  in
                                              uu____4053 :: uu____4060  in
                                            uu____4037 :: uu____4044  in
                                          uu____4021 :: uu____4028  in
                                        uu____4005 :: uu____4012  in
                                      let uu____4112 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____3996
                                        uu____4112
                                       in
                                    check_and_gen' "bind_wp"
                                      (Prims.of_int (2))
                                      FStar_Pervasives_Native.None
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      (FStar_Pervasives_Native.Some k))
                            in
                         log_combinator "bind_wp" bind_wp;
                         (let stronger =
                            let uu____4120 = fresh_a_and_wp ()  in
                            match uu____4120 with
                            | (a,wp_sort_a) ->
                                let uu____4133 = FStar_Syntax_Util.type_u ()
                                   in
                                (match uu____4133 with
                                 | (t,uu____4139) ->
                                     let k =
                                       let uu____4143 =
                                         let uu____4152 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____4159 =
                                           let uu____4168 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____4175 =
                                             let uu____4184 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____4184]  in
                                           uu____4168 :: uu____4175  in
                                         uu____4152 :: uu____4159  in
                                       let uu____4215 =
                                         FStar_Syntax_Syntax.mk_Total t  in
                                       FStar_Syntax_Util.arrow uu____4143
                                         uu____4215
                                        in
                                     check_and_gen' "stronger" Prims.int_one
                                       FStar_Pervasives_Native.None
                                       ed2.FStar_Syntax_Syntax.stronger
                                       (FStar_Pervasives_Native.Some k))
                             in
                          log_combinator "stronger" stronger;
                          (let match_wps =
                             let uu____4227 =
                               FStar_Syntax_Util.get_match_with_close_wps
                                 ed2.FStar_Syntax_Syntax.match_wps
                                in
                             match uu____4227 with
                             | (if_then_else1,ite_wp,close_wp) ->
                                 let if_then_else2 =
                                   let uu____4242 = fresh_a_and_wp ()  in
                                   match uu____4242 with
                                   | (a,wp_sort_a) ->
                                       let p =
                                         let uu____4256 =
                                           let uu____4259 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____4259
                                            in
                                         let uu____4260 =
                                           let uu____4261 =
                                             FStar_Syntax_Util.type_u ()  in
                                           FStar_All.pipe_right uu____4261
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____4256 uu____4260
                                          in
                                       let k =
                                         let uu____4273 =
                                           let uu____4282 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____4289 =
                                             let uu____4298 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 p
                                                in
                                             let uu____4305 =
                                               let uu____4314 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               let uu____4321 =
                                                 let uu____4330 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____4330]  in
                                               uu____4314 :: uu____4321  in
                                             uu____4298 :: uu____4305  in
                                           uu____4282 :: uu____4289  in
                                         let uu____4367 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a
                                            in
                                         FStar_Syntax_Util.arrow uu____4273
                                           uu____4367
                                          in
                                       check_and_gen' "if_then_else"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         if_then_else1
                                         (FStar_Pervasives_Native.Some k)
                                    in
                                 (log_combinator "if_then_else" if_then_else2;
                                  (let ite_wp1 =
                                     let uu____4375 = fresh_a_and_wp ()  in
                                     match uu____4375 with
                                     | (a,wp_sort_a) ->
                                         let k =
                                           let uu____4391 =
                                             let uu____4400 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____4407 =
                                               let uu____4416 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____4416]  in
                                             uu____4400 :: uu____4407  in
                                           let uu____4441 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____4391
                                             uu____4441
                                            in
                                         check_and_gen' "ite_wp"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           ite_wp
                                           (FStar_Pervasives_Native.Some k)
                                      in
                                   log_combinator "ite_wp" ite_wp1;
                                   (let close_wp1 =
                                      let uu____4449 = fresh_a_and_wp ()  in
                                      match uu____4449 with
                                      | (a,wp_sort_a) ->
                                          let b =
                                            let uu____4463 =
                                              let uu____4466 =
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____4466
                                               in
                                            let uu____4467 =
                                              let uu____4468 =
                                                FStar_Syntax_Util.type_u ()
                                                 in
                                              FStar_All.pipe_right uu____4468
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____4463 uu____4467
                                             in
                                          let wp_sort_b_a =
                                            let uu____4480 =
                                              let uu____4489 =
                                                let uu____4496 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    b
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____4496
                                                 in
                                              [uu____4489]  in
                                            let uu____4509 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4480 uu____4509
                                             in
                                          let k =
                                            let uu____4515 =
                                              let uu____4524 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4531 =
                                                let uu____4540 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b
                                                   in
                                                let uu____4547 =
                                                  let uu____4556 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_b_a
                                                     in
                                                  [uu____4556]  in
                                                uu____4540 :: uu____4547  in
                                              uu____4524 :: uu____4531  in
                                            let uu____4587 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4515 uu____4587
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
                                        FStar_Syntax_Syntax.ite_wp = ite_wp1;
                                        FStar_Syntax_Syntax.close_wp =
                                          close_wp1
                                      })))
                              in
                           let trivial =
                             let uu____4597 = fresh_a_and_wp ()  in
                             match uu____4597 with
                             | (a,wp_sort_a) ->
                                 let uu____4612 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____4612 with
                                  | (t,uu____4620) ->
                                      let k =
                                        let uu____4624 =
                                          let uu____4633 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4640 =
                                            let uu____4649 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a
                                               in
                                            [uu____4649]  in
                                          uu____4633 :: uu____4640  in
                                        let uu____4674 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____4624
                                          uu____4674
                                         in
                                      let trivial =
                                        let uu____4678 =
                                          FStar_All.pipe_right
                                            ed2.FStar_Syntax_Syntax.trivial
                                            FStar_Util.must
                                           in
                                        check_and_gen' "trivial"
                                          Prims.int_one
                                          FStar_Pervasives_Native.None
                                          uu____4678
                                          (FStar_Pervasives_Native.Some k)
                                         in
                                      (log_combinator "trivial" trivial;
                                       FStar_Pervasives_Native.Some trivial))
                              in
                           let uu____4693 =
                             let uu____4704 =
                               let uu____4705 =
                                 FStar_Syntax_Subst.compress
                                   (FStar_Pervasives_Native.snd
                                      ed2.FStar_Syntax_Syntax.repr)
                                  in
                               uu____4705.FStar_Syntax_Syntax.n  in
                             match uu____4704 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____4724 ->
                                 let repr =
                                   let uu____4726 = fresh_a_and_wp ()  in
                                   match uu____4726 with
                                   | (a,wp_sort_a) ->
                                       let uu____4739 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____4739 with
                                        | (t,uu____4745) ->
                                            let k =
                                              let uu____4749 =
                                                let uu____4758 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____4765 =
                                                  let uu____4774 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a
                                                     in
                                                  [uu____4774]  in
                                                uu____4758 :: uu____4765  in
                                              let uu____4799 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____4749 uu____4799
                                               in
                                            check_and_gen' "repr"
                                              Prims.int_one
                                              FStar_Pervasives_Native.None
                                              ed2.FStar_Syntax_Syntax.repr
                                              (FStar_Pervasives_Native.Some k))
                                    in
                                 (log_combinator "repr" repr;
                                  (let mk_repr' t wp =
                                     let uu____4819 =
                                       FStar_TypeChecker_Env.inst_tscheme
                                         repr
                                        in
                                     match uu____4819 with
                                     | (uu____4826,repr1) ->
                                         let repr2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.EraseUniverses;
                                             FStar_TypeChecker_Env.AllowUnboundUniverses]
                                             env repr1
                                            in
                                         let uu____4829 =
                                           let uu____4836 =
                                             let uu____4837 =
                                               let uu____4854 =
                                                 let uu____4865 =
                                                   FStar_All.pipe_right t
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____4882 =
                                                   let uu____4893 =
                                                     FStar_All.pipe_right wp
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____4893]  in
                                                 uu____4865 :: uu____4882  in
                                               (repr2, uu____4854)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____4837
                                              in
                                           FStar_Syntax_Syntax.mk uu____4836
                                            in
                                         uu____4829
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                      in
                                   let mk_repr a wp =
                                     let uu____4959 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     mk_repr' uu____4959 wp  in
                                   let destruct_repr t =
                                     let uu____4974 =
                                       let uu____4975 =
                                         FStar_Syntax_Subst.compress t  in
                                       uu____4975.FStar_Syntax_Syntax.n  in
                                     match uu____4974 with
                                     | FStar_Syntax_Syntax.Tm_app
                                         (uu____4986,(t1,uu____4988)::
                                          (wp,uu____4990)::[])
                                         -> (t1, wp)
                                     | uu____5049 ->
                                         failwith "Unexpected repr type"
                                      in
                                   let return_repr =
                                     let uu____5060 = fresh_a_and_wp ()  in
                                     match uu____5060 with
                                     | (a,uu____5068) ->
                                         let x_a =
                                           let uu____5074 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x_a"
                                             FStar_Pervasives_Native.None
                                             uu____5074
                                            in
                                         let res =
                                           let wp =
                                             let uu____5082 =
                                               let uu____5087 =
                                                 let uu____5088 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     ret_wp
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5088
                                                   FStar_Pervasives_Native.snd
                                                  in
                                               let uu____5097 =
                                                 let uu____5098 =
                                                   let uu____5107 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____5107
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5116 =
                                                   let uu____5127 =
                                                     let uu____5136 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____5136
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____5127]  in
                                                 uu____5098 :: uu____5116  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____5087 uu____5097
                                                in
                                             uu____5082
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           mk_repr a wp  in
                                         let k =
                                           let uu____5172 =
                                             let uu____5181 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____5188 =
                                               let uu____5197 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x_a
                                                  in
                                               [uu____5197]  in
                                             uu____5181 :: uu____5188  in
                                           let uu____5222 =
                                             FStar_Syntax_Syntax.mk_Total res
                                              in
                                           FStar_Syntax_Util.arrow uu____5172
                                             uu____5222
                                            in
                                         let uu____5225 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env k
                                            in
                                         (match uu____5225 with
                                          | (k1,uu____5233,uu____5234) ->
                                              let env1 =
                                                let uu____5238 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____5238
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
                                        let uu____5249 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Parser_Const.range_0
                                            FStar_Syntax_Syntax.delta_constant
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_All.pipe_right uu____5249
                                          FStar_Syntax_Syntax.fv_to_tm
                                         in
                                      let uu____5250 = fresh_a_and_wp ()  in
                                      match uu____5250 with
                                      | (a,wp_sort_a) ->
                                          let uu____5263 = fresh_a_and_wp ()
                                             in
                                          (match uu____5263 with
                                           | (b,wp_sort_b) ->
                                               let wp_sort_a_b =
                                                 let uu____5279 =
                                                   let uu____5288 =
                                                     let uu____5295 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____5295
                                                      in
                                                   [uu____5288]  in
                                                 let uu____5308 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     wp_sort_b
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____5279 uu____5308
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
                                                 let uu____5316 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a
                                                    in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "x_a"
                                                   FStar_Pervasives_Native.None
                                                   uu____5316
                                                  in
                                               let wp_g_x =
                                                 let uu____5321 =
                                                   let uu____5326 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       wp_g
                                                      in
                                                   let uu____5327 =
                                                     let uu____5328 =
                                                       let uu____5337 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____5337
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____5328]  in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     uu____5326 uu____5327
                                                    in
                                                 uu____5321
                                                   FStar_Pervasives_Native.None
                                                   FStar_Range.dummyRange
                                                  in
                                               let res =
                                                 let wp =
                                                   let uu____5368 =
                                                     let uu____5373 =
                                                       let uu____5374 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           bind_wp
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____5374
                                                         FStar_Pervasives_Native.snd
                                                        in
                                                     let uu____5383 =
                                                       let uu____5384 =
                                                         let uu____5387 =
                                                           let uu____5390 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               a
                                                              in
                                                           let uu____5391 =
                                                             let uu____5394 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 b
                                                                in
                                                             let uu____5395 =
                                                               let uu____5398
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               let uu____5399
                                                                 =
                                                                 let uu____5402
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                    in
                                                                 [uu____5402]
                                                                  in
                                                               uu____5398 ::
                                                                 uu____5399
                                                                in
                                                             uu____5394 ::
                                                               uu____5395
                                                              in
                                                           uu____5390 ::
                                                             uu____5391
                                                            in
                                                         r :: uu____5387  in
                                                       FStar_List.map
                                                         FStar_Syntax_Syntax.as_arg
                                                         uu____5384
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____5373 uu____5383
                                                      in
                                                   uu____5368
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 mk_repr b wp  in
                                               let maybe_range_arg =
                                                 let uu____5420 =
                                                   FStar_Util.for_some
                                                     (FStar_Syntax_Util.attr_eq
                                                        FStar_Syntax_Util.dm4f_bind_range_attr)
                                                     ed2.FStar_Syntax_Syntax.eff_attrs
                                                    in
                                                 if uu____5420
                                                 then
                                                   let uu____5431 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       FStar_Syntax_Syntax.t_range
                                                      in
                                                   let uu____5438 =
                                                     let uu____5447 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     [uu____5447]  in
                                                   uu____5431 :: uu____5438
                                                 else []  in
                                               let k =
                                                 let uu____5483 =
                                                   let uu____5492 =
                                                     let uu____5501 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____5508 =
                                                       let uu____5517 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           b
                                                          in
                                                       [uu____5517]  in
                                                     uu____5501 :: uu____5508
                                                      in
                                                   let uu____5542 =
                                                     let uu____5551 =
                                                       let uu____5560 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           wp_f
                                                          in
                                                       let uu____5567 =
                                                         let uu____5576 =
                                                           let uu____5583 =
                                                             let uu____5584 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_f
                                                                in
                                                             mk_repr a
                                                               uu____5584
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____5583
                                                            in
                                                         let uu____5585 =
                                                           let uu____5594 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               wp_g
                                                              in
                                                           let uu____5601 =
                                                             let uu____5610 =
                                                               let uu____5617
                                                                 =
                                                                 let uu____5618
                                                                   =
                                                                   let uu____5627
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                   [uu____5627]
                                                                    in
                                                                 let uu____5646
                                                                   =
                                                                   let uu____5649
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                   FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____5649
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   uu____5618
                                                                   uu____5646
                                                                  in
                                                               FStar_Syntax_Syntax.null_binder
                                                                 uu____5617
                                                                in
                                                             [uu____5610]  in
                                                           uu____5594 ::
                                                             uu____5601
                                                            in
                                                         uu____5576 ::
                                                           uu____5585
                                                          in
                                                       uu____5560 ::
                                                         uu____5567
                                                        in
                                                     FStar_List.append
                                                       maybe_range_arg
                                                       uu____5551
                                                      in
                                                   FStar_List.append
                                                     uu____5492 uu____5542
                                                    in
                                                 let uu____5694 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     res
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____5483 uu____5694
                                                  in
                                               let uu____5697 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env k
                                                  in
                                               (match uu____5697 with
                                                | (k1,uu____5705,uu____5706)
                                                    ->
                                                    let env1 =
                                                      FStar_TypeChecker_Env.set_range
                                                        env
                                                        (FStar_Pervasives_Native.snd
                                                           ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                       in
                                                    let env2 =
                                                      FStar_All.pipe_right
                                                        (let uu___647_5718 =
                                                           env1  in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.instantiate_imp);
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             = true;
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.try_solve_implicits_hook
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___647_5718.FStar_TypeChecker_Env.strict_args_tab)
                                                         })
                                                        (fun _5720  ->
                                                           FStar_Pervasives_Native.Some
                                                             _5720)
                                                       in
                                                    check_and_gen'
                                                      "bind_repr"
                                                      (Prims.of_int (2)) env2
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
                                         (let uu____5747 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env, act)
                                            else
                                              (let uu____5761 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____5761 with
                                               | (usubst,uvs) ->
                                                   let uu____5784 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env uvs
                                                      in
                                                   let uu____5785 =
                                                     let uu___660_5786 = act
                                                        in
                                                     let uu____5787 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____5788 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___660_5786.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___660_5786.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___660_5786.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____5787;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____5788
                                                     }  in
                                                   (uu____5784, uu____5785))
                                             in
                                          match uu____5747 with
                                          | (env1,act1) ->
                                              let act_typ =
                                                let uu____5792 =
                                                  let uu____5793 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____5793.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____5792 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs1,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____5819 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____5819
                                                    then
                                                      let uu____5822 =
                                                        let uu____5825 =
                                                          let uu____5826 =
                                                            let uu____5827 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____5827
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____5826
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____5825
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____5822
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____5850 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____5851 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env1 act_typ
                                                 in
                                              (match uu____5851 with
                                               | (act_typ1,uu____5859,g_t) ->
                                                   let env' =
                                                     let uu___677_5862 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env1 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.fv_delta_depths);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.try_solve_implicits_hook
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.postprocess);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.nbe
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.nbe);
                                                       FStar_TypeChecker_Env.strict_args_tab
                                                         =
                                                         (uu___677_5862.FStar_TypeChecker_Env.strict_args_tab)
                                                     }  in
                                                   ((let uu____5865 =
                                                       FStar_TypeChecker_Env.debug
                                                         env1
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____5865
                                                     then
                                                       let uu____5869 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____5871 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____5873 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____5869
                                                         uu____5871
                                                         uu____5873
                                                     else ());
                                                    (let uu____5878 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____5878 with
                                                     | (act_defn,uu____5886,g_a)
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
                                                         let uu____5890 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1,c) ->
                                                               let uu____5926
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c
                                                                  in
                                                               (match uu____5926
                                                                with
                                                                | (bs2,uu____5938)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____5945
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____5945
                                                                     in
                                                                    let uu____5948
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____5948
                                                                    with
                                                                    | 
                                                                    (k1,uu____5962,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____5966 ->
                                                               let uu____5967
                                                                 =
                                                                 let uu____5973
                                                                   =
                                                                   let uu____5975
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____5977
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____5975
                                                                    uu____5977
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____5973)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____5967
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____5890
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env1
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____5995
                                                                  =
                                                                  let uu____5996
                                                                    =
                                                                    let uu____5997
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____5997
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____5996
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env1
                                                                  uu____5995);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____5999
                                                                    =
                                                                    let uu____6000
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6000.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____5999
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____6025
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____6025
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____6032
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6032
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____6052
                                                                    =
                                                                    let uu____6053
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____6053]
                                                                     in
                                                                    let uu____6054
                                                                    =
                                                                    let uu____6065
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6065]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6052;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6054;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6090
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6090))
                                                                  | uu____6093
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____6095
                                                                  =
                                                                  if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                  then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                  else
                                                                    (
                                                                    let uu____6117
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6117))
                                                                   in
                                                                match uu____6095
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
                                                                    let uu___727_6136
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___727_6136.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___727_6136.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___727_6136.FStar_Syntax_Syntax.action_params);
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
                                     (repr, return_repr, bind_repr, actions)))))
                              in
                           match uu____4693 with
                           | (repr,return_repr,bind_repr,actions) ->
                               let cl ts =
                                 let ts1 =
                                   FStar_Syntax_Subst.close_tscheme ed_bs ts
                                    in
                                 let ed_univs_closing =
                                   FStar_Syntax_Subst.univ_var_closing
                                     ed_univs
                                    in
                                 let uu____6161 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length ed_bs)
                                     ed_univs_closing
                                    in
                                 FStar_Syntax_Subst.subst_tscheme uu____6161
                                   ts1
                                  in
                               let ed3 =
                                 let uu___739_6171 = ed2  in
                                 let uu____6172 = cl signature  in
                                 let uu____6173 = cl ret_wp  in
                                 let uu____6174 = cl bind_wp  in
                                 let uu____6175 = cl stronger  in
                                 let uu____6176 =
                                   FStar_Syntax_Util.map_match_wps cl
                                     match_wps
                                    in
                                 let uu____6181 =
                                   FStar_Util.map_opt trivial cl  in
                                 let uu____6184 = cl repr  in
                                 let uu____6185 = cl return_repr  in
                                 let uu____6186 = cl bind_repr  in
                                 let uu____6187 =
                                   FStar_List.map
                                     (fun a  ->
                                        let uu___742_6195 = a  in
                                        let uu____6196 =
                                          let uu____6197 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_All.pipe_right uu____6197
                                            FStar_Pervasives_Native.snd
                                           in
                                        let uu____6222 =
                                          let uu____6223 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_All.pipe_right uu____6223
                                            FStar_Pervasives_Native.snd
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            (uu___742_6195.FStar_Syntax_Syntax.action_name);
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (uu___742_6195.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (uu___742_6195.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (uu___742_6195.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____6196;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____6222
                                        }) actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___739_6171.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___739_6171.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___739_6171.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs =
                                     (uu___739_6171.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders =
                                     (uu___739_6171.FStar_Syntax_Syntax.binders);
                                   FStar_Syntax_Syntax.signature = uu____6172;
                                   FStar_Syntax_Syntax.ret_wp = uu____6173;
                                   FStar_Syntax_Syntax.bind_wp = uu____6174;
                                   FStar_Syntax_Syntax.stronger = uu____6175;
                                   FStar_Syntax_Syntax.match_wps = uu____6176;
                                   FStar_Syntax_Syntax.trivial = uu____6181;
                                   FStar_Syntax_Syntax.repr = uu____6184;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____6185;
                                   FStar_Syntax_Syntax.bind_repr = uu____6186;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     FStar_Pervasives_Native.None;
                                   FStar_Syntax_Syntax.actions = uu____6187;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___739_6171.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____6249 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____6249
                                 then
                                   let uu____6254 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked effect declaration:\n\t%s\n"
                                     uu____6254
                                 else ());
                                ed3))))))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun ed  ->
      (if ed.FStar_Syntax_Syntax.is_layered
       then tc_layered_eff_decl
       else tc_non_layered_eff_decl) env ed
  
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
        let fail1 uu____6307 =
          let uu____6308 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____6314 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____6308 uu____6314  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____6358)::(wp,uu____6360)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____6389 -> fail1 ())
        | uu____6390 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____6403 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____6403
       then
         let uu____6408 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____6408
       else ());
      (let uu____6413 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____6413 with
       | (us,lift) ->
           let r = lift.FStar_Syntax_Syntax.pos  in
           (if (FStar_List.length us) <> Prims.int_zero
            then
              (let uu____6447 =
                 let uu____6449 = FStar_Syntax_Print.sub_eff_to_string sub1
                    in
                 Prims.op_Hat
                   "Unexpected number of universes in typechecking %s"
                   uu____6449
                  in
               failwith uu____6447)
            else ();
            (let uu____6454 =
               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env0 lift  in
             match uu____6454 with
             | (lift1,lc,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env0 g;
                  (let lift_ty =
                     FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                       (FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Beta] env0)
                      in
                   (let uu____6471 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                        (FStar_Options.Other "LayeredEffects")
                       in
                    if uu____6471
                    then
                      let uu____6476 =
                        FStar_Syntax_Print.term_to_string lift1  in
                      let uu____6478 =
                        FStar_Syntax_Print.term_to_string lift_ty  in
                      FStar_Util.print2
                        "Typechecked lift: %s and lift_ty: %s\n" uu____6476
                        uu____6478
                    else ());
                   (let uu____6483 =
                      let uu____6490 =
                        let uu____6495 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____6495
                          (fun uu____6512  ->
                             match uu____6512 with
                             | (t,u) ->
                                 let uu____6523 =
                                   let uu____6524 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____6524
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____6523, u))
                         in
                      match uu____6490 with
                      | (a,u_a) ->
                          let uu____6534 =
                            let uu____6541 =
                              FStar_TypeChecker_Env.lookup_effect_lid env0
                                sub1.FStar_Syntax_Syntax.source
                               in
                            monad_signature env0
                              sub1.FStar_Syntax_Syntax.source uu____6541
                             in
                          (match uu____6534 with
                           | (a',wp_sort_a') ->
                               let src_wp_sort_a =
                                 let uu____6555 =
                                   let uu____6558 =
                                     let uu____6559 =
                                       let uu____6566 =
                                         let uu____6569 =
                                           FStar_All.pipe_right a
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_All.pipe_right uu____6569
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       (a', uu____6566)  in
                                     FStar_Syntax_Syntax.NT uu____6559  in
                                   [uu____6558]  in
                                 FStar_Syntax_Subst.subst uu____6555
                                   wp_sort_a'
                                  in
                               let wp =
                                 let uu____6589 =
                                   FStar_Syntax_Syntax.gen_bv "wp"
                                     FStar_Pervasives_Native.None
                                     src_wp_sort_a
                                    in
                                 FStar_All.pipe_right uu____6589
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               let rest_bs =
                                 let uu____6606 =
                                   let uu____6607 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____6607.FStar_Syntax_Syntax.n  in
                                 match uu____6606 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____6619) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (3))
                                     ->
                                     let uu____6647 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____6647 with
                                      | (a'1,uu____6657)::(wp',uu____6659)::bs1
                                          ->
                                          let uu____6689 =
                                            FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one) bs1
                                             in
                                          (match uu____6689 with
                                           | (bs2,uu____6732) ->
                                               let substs =
                                                 let uu____6768 =
                                                   let uu____6769 =
                                                     let uu____6776 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a'1, uu____6776)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____6769
                                                    in
                                                 let uu____6783 =
                                                   let uu____6786 =
                                                     let uu____6787 =
                                                       let uu____6794 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              wp)
                                                          in
                                                       (wp', uu____6794)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____6787
                                                      in
                                                   [uu____6786]  in
                                                 uu____6768 :: uu____6783  in
                                               FStar_Syntax_Subst.subst_binders
                                                 substs bs2)
                                      | uu____6801 -> failwith "Impossible!")
                                 | uu____6811 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_UnexpectedEffect,
                                         "") r
                                  in
                               let f =
                                 let f_sort =
                                   let uu____6832 =
                                     let uu____6841 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_Syntax_Syntax.t_unit
                                        in
                                     [uu____6841]  in
                                   let uu____6860 =
                                     let uu____6863 =
                                       let uu____6864 =
                                         let uu____6867 =
                                           FStar_All.pipe_right a
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_All.pipe_right uu____6867
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       let uu____6878 =
                                         let uu____6889 =
                                           let uu____6898 =
                                             let uu____6899 =
                                               FStar_All.pipe_right wp
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____6899
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_All.pipe_right uu____6898
                                             FStar_Syntax_Syntax.as_arg
                                            in
                                         [uu____6889]  in
                                       {
                                         FStar_Syntax_Syntax.comp_univs =
                                           [u_a];
                                         FStar_Syntax_Syntax.effect_name =
                                           (sub1.FStar_Syntax_Syntax.source);
                                         FStar_Syntax_Syntax.result_typ =
                                           uu____6864;
                                         FStar_Syntax_Syntax.effect_args =
                                           uu____6878;
                                         FStar_Syntax_Syntax.flags = []
                                       }  in
                                     FStar_Syntax_Syntax.mk_Comp uu____6863
                                      in
                                   FStar_Syntax_Util.arrow uu____6832
                                     uu____6860
                                    in
                                 let uu____6932 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort
                                    in
                                 FStar_All.pipe_right uu____6932
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               let bs = a :: wp ::
                                 (FStar_List.append rest_bs [f])  in
                               let uu____6979 =
                                 let uu____6984 =
                                   FStar_TypeChecker_Env.push_binders env0 bs
                                    in
                                 let uu____6985 =
                                   let uu____6986 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____6986
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_layered_effect_repr_en
                                   uu____6984 r
                                   sub1.FStar_Syntax_Syntax.target u_a
                                   uu____6985
                                  in
                               (match uu____6979 with
                                | (repr,g_repr) ->
                                    let uu____7003 =
                                      let uu____7006 =
                                        let uu____7009 =
                                          let uu____7012 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_All.pipe_right uu____7012
                                            (fun _7015  ->
                                               FStar_Pervasives_Native.Some
                                                 _7015)
                                           in
                                        FStar_Syntax_Syntax.mk_Total' repr
                                          uu____7009
                                         in
                                      FStar_Syntax_Util.arrow bs uu____7006
                                       in
                                    (uu____7003, g_repr)))
                       in
                    match uu____6483 with
                    | (k,g_k) ->
                        ((let uu____7025 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____7025
                          then
                            let uu____7030 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1 "Before unification k: %s\n"
                              uu____7030
                          else ());
                         (let g1 = FStar_TypeChecker_Rel.teq env0 lift_ty k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env0 g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env0 g1;
                          (let uu____7039 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects")
                              in
                           if uu____7039
                           then
                             let uu____7044 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____7044
                           else ());
                          (let uu____7049 =
                             FStar_TypeChecker_Util.generalize_universes env0
                               lift1
                              in
                           match uu____7049 with
                           | (us1,lift2) ->
                               let lift_wp =
                                 let uu____7063 =
                                   let uu____7064 =
                                     let uu____7069 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us1
                                        in
                                     FStar_TypeChecker_Normalize.remove_uvar_solutions
                                       uu____7069
                                      in
                                   FStar_All.pipe_right k uu____7064  in
                                 FStar_All.pipe_right uu____7063
                                   (FStar_Syntax_Subst.close_univ_vars us1)
                                  in
                               let sub2 =
                                 let uu___839_7073 = sub1  in
                                 {
                                   FStar_Syntax_Syntax.source =
                                     (uu___839_7073.FStar_Syntax_Syntax.source);
                                   FStar_Syntax_Syntax.target =
                                     (uu___839_7073.FStar_Syntax_Syntax.target);
                                   FStar_Syntax_Syntax.lift_wp =
                                     (FStar_Pervasives_Native.Some
                                        (us1, lift_wp));
                                   FStar_Syntax_Syntax.lift =
                                     (FStar_Pervasives_Native.Some
                                        (us1, lift2))
                                 }  in
                               ((let uu____7083 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____7083
                                 then
                                   let uu____7088 =
                                     FStar_Syntax_Print.sub_eff_to_string
                                       sub2
                                      in
                                   FStar_Util.print1 "Final sub_effect: %s\n"
                                     uu____7088
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
          (let uu____7114 =
             let uu____7121 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____7121
              in
           match uu____7114 with
           | (a,wp_a_src) ->
               let uu____7128 =
                 let uu____7135 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____7135
                  in
               (match uu____7128 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____7143 =
                        let uu____7146 =
                          let uu____7147 =
                            let uu____7154 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____7154)  in
                          FStar_Syntax_Syntax.NT uu____7147  in
                        [uu____7146]  in
                      FStar_Syntax_Subst.subst uu____7143 wp_b_tgt  in
                    let expected_k =
                      let uu____7162 =
                        let uu____7171 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____7178 =
                          let uu____7187 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____7187]  in
                        uu____7171 :: uu____7178  in
                      let uu____7212 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____7162 uu____7212  in
                    let repr_type eff_name a1 wp =
                      (let uu____7234 =
                         let uu____7236 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____7236  in
                       if uu____7234
                       then
                         let uu____7239 =
                           let uu____7245 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____7245)
                            in
                         let uu____7249 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____7239 uu____7249
                       else ());
                      (let uu____7252 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____7252 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ed.FStar_Syntax_Syntax.repr
                              in
                           let uu____7285 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____7286 =
                             let uu____7293 =
                               let uu____7294 =
                                 let uu____7311 =
                                   let uu____7322 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____7331 =
                                     let uu____7342 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____7342]  in
                                   uu____7322 :: uu____7331  in
                                 (repr, uu____7311)  in
                               FStar_Syntax_Syntax.Tm_app uu____7294  in
                             FStar_Syntax_Syntax.mk uu____7293  in
                           uu____7286 FStar_Pervasives_Native.None uu____7285)
                       in
                    let uu____7387 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____7560 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____7571 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____7571 with
                              | (usubst,uvs1) ->
                                  let uu____7594 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____7595 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____7594, uu____7595)
                            else (env, lift_wp)  in
                          (match uu____7560 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      tc_check_trivial_guard env1 lift_wp1
                                        expected_k
                                       in
                                    let uu____7645 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____7645))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____7716 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____7731 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____7731 with
                              | (usubst,uvs) ->
                                  let uu____7756 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____7756)
                            else ([], lift)  in
                          (match uu____7716 with
                           | (uvs,lift1) ->
                               ((let uu____7792 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____7792
                                 then
                                   let uu____7796 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____7796
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____7802 =
                                   let uu____7809 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____7809 lift1
                                    in
                                 match uu____7802 with
                                 | (lift2,comp,uu____7834) ->
                                     let uu____7835 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____7835 with
                                      | (uu____7864,lift_wp,lift_elab) ->
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
                                            let uu____7896 =
                                              let uu____7907 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____7907
                                               in
                                            let uu____7924 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____7896, uu____7924)
                                          else
                                            (let uu____7953 =
                                               let uu____7964 =
                                                 let uu____7973 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____7973)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____7964
                                                in
                                             let uu____7988 =
                                               let uu____7997 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____7997)  in
                                             (uu____7953, uu____7988))))))
                       in
                    (match uu____7387 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___919_8061 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___919_8061.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___919_8061.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___919_8061.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___919_8061.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___919_8061.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___919_8061.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___919_8061.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___919_8061.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___919_8061.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___919_8061.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___919_8061.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___919_8061.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___919_8061.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___919_8061.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___919_8061.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___919_8061.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___919_8061.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___919_8061.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___919_8061.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___919_8061.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___919_8061.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___919_8061.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___919_8061.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___919_8061.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___919_8061.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___919_8061.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___919_8061.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___919_8061.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___919_8061.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___919_8061.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___919_8061.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___919_8061.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___919_8061.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___919_8061.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___919_8061.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___919_8061.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___919_8061.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___919_8061.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___919_8061.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___919_8061.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___919_8061.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___919_8061.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___919_8061.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___919_8061.FStar_TypeChecker_Env.strict_args_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____8094 =
                                 let uu____8099 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____8099 with
                                 | (usubst,uvs1) ->
                                     let uu____8122 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____8123 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____8122, uu____8123)
                                  in
                               (match uu____8094 with
                                | (env2,lift2) ->
                                    let uu____8128 =
                                      let uu____8135 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____8135
                                       in
                                    (match uu____8128 with
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
                                             let uu____8161 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____8162 =
                                               let uu____8169 =
                                                 let uu____8170 =
                                                   let uu____8187 =
                                                     let uu____8198 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____8207 =
                                                       let uu____8218 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____8218]  in
                                                     uu____8198 :: uu____8207
                                                      in
                                                   (lift_wp1, uu____8187)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8170
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____8169
                                                in
                                             uu____8162
                                               FStar_Pervasives_Native.None
                                               uu____8161
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____8266 =
                                             let uu____8275 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____8282 =
                                               let uu____8291 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____8298 =
                                                 let uu____8307 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____8307]  in
                                               uu____8291 :: uu____8298  in
                                             uu____8275 :: uu____8282  in
                                           let uu____8338 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow uu____8266
                                             uu____8338
                                            in
                                         let uu____8341 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____8341 with
                                          | (expected_k2,uu____8351,uu____8352)
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
                                                   let uu____8360 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____8360))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____8368 =
                             let uu____8370 =
                               let uu____8372 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____8372
                                 FStar_List.length
                                in
                             uu____8370 <> Prims.int_one  in
                           if uu____8368
                           then
                             let uu____8395 =
                               let uu____8401 =
                                 let uu____8403 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____8405 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____8407 =
                                   let uu____8409 =
                                     let uu____8411 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8411
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____8409
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____8403 uu____8405 uu____8407
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____8401)
                                in
                             FStar_Errors.raise_error uu____8395 r
                           else ());
                          (let uu____8438 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____8441 =
                                  let uu____8443 =
                                    let uu____8446 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____8446
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8443
                                    FStar_List.length
                                   in
                                uu____8441 <> Prims.int_one)
                              in
                           if uu____8438
                           then
                             let uu____8484 =
                               let uu____8490 =
                                 let uu____8492 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____8494 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____8496 =
                                   let uu____8498 =
                                     let uu____8500 =
                                       let uu____8503 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____8503
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8500
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____8498
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____8492 uu____8494 uu____8496
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____8490)
                                in
                             FStar_Errors.raise_error uu____8484 r
                           else ());
                          (let uu___956_8545 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___956_8545.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___956_8545.FStar_Syntax_Syntax.target);
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
    fun uu____8576  ->
      fun r  ->
        match uu____8576 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____8599 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____8627 = FStar_Syntax_Subst.univ_var_opening uvs  in
                 match uu____8627 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____8658 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____8658 c  in
                     let uu____8667 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____8667, uvs1, tps1, c1))
               in
            (match uu____8599 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____8687 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____8687 with
                  | (tps2,c2) ->
                      let uu____8702 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____8702 with
                       | (tps3,env3,us) ->
                           let uu____8720 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____8720 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____8746)::uu____8747 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____8766 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____8774 =
                                    let uu____8776 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____8776  in
                                  if uu____8774
                                  then
                                    let uu____8779 =
                                      let uu____8785 =
                                        let uu____8787 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____8789 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____8787 uu____8789
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____8785)
                                       in
                                    FStar_Errors.raise_error uu____8779 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____8797 =
                                    let uu____8798 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____8798
                                     in
                                  match uu____8797 with
                                  | (uvs2,t) ->
                                      let uu____8827 =
                                        let uu____8832 =
                                          let uu____8845 =
                                            let uu____8846 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____8846.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____8845)  in
                                        match uu____8832 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____8861,c5)) -> ([], c5)
                                        | (uu____8903,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____8942 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____8827 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____8974 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____8974 with
                                               | (uu____8979,t1) ->
                                                   let uu____8981 =
                                                     let uu____8987 =
                                                       let uu____8989 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____8991 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____8995 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____8989
                                                         uu____8991
                                                         uu____8995
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____8987)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____8981 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  