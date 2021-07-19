open Prims
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.unfold_whnf'
    [FStar_TypeChecker_Env.AllowUnboundUniverses]
let (tc_tycon :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_TypeChecker_Env.env_t * FStar_Syntax_Syntax.sigelt *
        FStar_Syntax_Syntax.universe * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun s ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (tc, uvs, tps, k, mutuals, data) ->
          let env0 = env in
          let uu___ = FStar_Syntax_Subst.univ_var_opening uvs in
          (match uu___ with
           | (usubst, uvs1) ->
               let uu___1 =
                 let uu___2 = FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                 let uu___3 = FStar_Syntax_Subst.subst_binders usubst tps in
                 let uu___4 =
                   let uu___5 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst in
                   FStar_Syntax_Subst.subst uu___5 k in
                 (uu___2, uu___3, uu___4) in
               (match uu___1 with
                | (env1, tps1, k1) ->
                    let uu___2 = FStar_Syntax_Subst.open_term tps1 k1 in
                    (match uu___2 with
                     | (tps2, k2) ->
                         let uu___3 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2 in
                         (match uu___3 with
                          | (tps3, env_tps, guard_params, us) ->
                              let uu___4 =
                                let uu___5 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2 in
                                match uu___5 with
                                | (k3, uu___6, g) ->
                                    let k4 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Exclude
                                           FStar_TypeChecker_Env.Iota;
                                        FStar_TypeChecker_Env.Exclude
                                          FStar_TypeChecker_Env.Zeta;
                                        FStar_TypeChecker_Env.Eager_unfolding;
                                        FStar_TypeChecker_Env.NoFullNorm;
                                        FStar_TypeChecker_Env.Exclude
                                          FStar_TypeChecker_Env.Beta] env_tps
                                        k3 in
                                    let uu___7 =
                                      FStar_Syntax_Util.arrow_formals k4 in
                                    let uu___8 =
                                      let uu___9 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu___9 in
                                    (uu___7, uu___8) in
                              (match uu___4 with
                               | ((indices, t), guard) ->
                                   let k3 =
                                     let uu___5 =
                                       FStar_Syntax_Syntax.mk_Total t in
                                     FStar_Syntax_Util.arrow indices uu___5 in
                                   let uu___5 = FStar_Syntax_Util.type_u () in
                                   (match uu___5 with
                                    | (t_type, u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu___6 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq) in
                                              Prims.op_Negation uu___6))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type) in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu___7 =
                                              let uu___8 =
                                                let uu___9 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t in
                                                let uu___10 =
                                                  FStar_Ident.string_of_lid
                                                    tc in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu___9 uu___10 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu___8) in
                                            FStar_Errors.raise_error uu___7
                                              s.FStar_Syntax_Syntax.sigrng)
                                         else ();
                                         (let usubst1 =
                                            FStar_Syntax_Subst.univ_var_closing
                                              uvs1 in
                                          let guard1 =
                                            FStar_TypeChecker_Util.close_guard_implicits
                                              env1 false tps3 guard in
                                          let t_tc =
                                            let uu___7 =
                                              let uu___8 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1) in
                                              let uu___9 =
                                                let uu___10 =
                                                  let uu___11 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1 in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu___11 in
                                                FStar_All.pipe_right indices
                                                  uu___10 in
                                              FStar_List.append uu___8 uu___9 in
                                            let uu___8 =
                                              let uu___9 =
                                                let uu___10 =
                                                  let uu___11 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1 in
                                                  FStar_Syntax_Subst.subst
                                                    uu___11 in
                                                FStar_All.pipe_right t
                                                  uu___10 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu___9 in
                                            FStar_Syntax_Util.arrow uu___7
                                              uu___8 in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3 in
                                          let uu___7 =
                                            let uu___8 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4 in
                                            let uu___9 =
                                              let uu___10 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1 in
                                              FStar_Syntax_Subst.subst
                                                uu___10 k4 in
                                            (uu___8, uu___9) in
                                          match uu___7 with
                                          | (tps5, k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None in
                                              let uu___8 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs1 t_tc in
                                              (match uu___8 with
                                               | (uvs2, t_tc1) ->
                                                   let uu___9 =
                                                     FStar_TypeChecker_Env.push_let_binding
                                                       env0
                                                       (FStar_Pervasives.Inr
                                                          fv_tc)
                                                       (uvs2, t_tc1) in
                                                   (uu___9,
                                                     (let uu___10 = s in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_inductive_typ
                                                             (tc, uvs2, tps5,
                                                               k5, mutuals,
                                                               data));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___10.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___10.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___10.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___10.FStar_Syntax_Syntax.sigattrs);
                                                        FStar_Syntax_Syntax.sigopts
                                                          =
                                                          (uu___10.FStar_Syntax_Syntax.sigopts)
                                                      }), u, guard1))))))))))
      | uu___ -> failwith "impossible"
let (tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun tcs ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (c, _uvs, t, tc_lid, ntps, mutual_tcs) ->
            let uu___ = FStar_Syntax_Subst.univ_var_opening _uvs in
            (match uu___ with
             | (usubst, _uvs1) ->
                 let uu___1 =
                   let uu___2 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1 in
                   let uu___3 = FStar_Syntax_Subst.subst usubst t in
                   (uu___2, uu___3) in
                 (match uu___1 with
                  | (env1, t1) ->
                      let uu___2 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu___3 ->
                               match uu___3 with
                               | (se1, u_tc) ->
                                   let uu___4 =
                                     let uu___5 =
                                       let uu___6 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Util.must uu___6 in
                                     FStar_Ident.lid_equals tc_lid uu___5 in
                                   if uu___4
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu___5, uu___6, tps, uu___7,
                                           uu___8, uu___9)
                                          ->
                                          let tps1 =
                                            let uu___10 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst) in
                                            FStar_All.pipe_right uu___10
                                              (FStar_List.map
                                                 (fun x ->
                                                    let uu___11 = x in
                                                    {
                                                      FStar_Syntax_Syntax.binder_bv
                                                        =
                                                        (uu___11.FStar_Syntax_Syntax.binder_bv);
                                                      FStar_Syntax_Syntax.binder_qual
                                                        =
                                                        (FStar_Pervasives_Native.Some
                                                           FStar_Syntax_Syntax.imp_tag);
                                                      FStar_Syntax_Syntax.binder_attrs
                                                        =
                                                        (uu___11.FStar_Syntax_Syntax.binder_attrs)
                                                    })) in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1 in
                                          let uu___10 =
                                            let uu___11 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2 in
                                            (uu___11, tps2, u_tc) in
                                          FStar_Pervasives_Native.Some
                                            uu___10
                                      | uu___5 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None) in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None ->
                            let uu___3 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid in
                            if uu___3
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng in
                      (match uu___2 with
                       | (env2, tps, u_tc) ->
                           let uu___3 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1 in
                             let uu___4 =
                               let uu___5 = FStar_Syntax_Subst.compress t2 in
                               uu___5.FStar_Syntax_Syntax.n in
                             match uu___4 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs, res) ->
                                 let uu___5 = FStar_Util.first_N ntps bs in
                                 (match uu___5 with
                                  | (uu___6, bs') ->
                                      let t3 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (bs', res))
                                          t2.FStar_Syntax_Syntax.pos in
                                      let subst =
                                        FStar_All.pipe_right tps
                                          (FStar_List.mapi
                                             (fun i ->
                                                fun uu___7 ->
                                                  match uu___7 with
                                                  | {
                                                      FStar_Syntax_Syntax.binder_bv
                                                        = x;
                                                      FStar_Syntax_Syntax.binder_qual
                                                        = uu___8;
                                                      FStar_Syntax_Syntax.binder_attrs
                                                        = uu___9;_}
                                                      ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            (Prims.int_one +
                                                               i)), x))) in
                                      let uu___7 =
                                        let uu___8 =
                                          FStar_Syntax_Subst.subst subst t3 in
                                        FStar_Syntax_Util.arrow_formals_comp
                                          uu___8 in
                                      (match uu___7 with
                                       | (bs1, c1) ->
                                           let uu___8 =
                                             (FStar_Options.ml_ish ()) ||
                                               (FStar_Syntax_Util.is_total_comp
                                                  c1) in
                                           if uu___8
                                           then
                                             (bs1,
                                               (FStar_Syntax_Util.comp_result
                                                  c1))
                                           else
                                             (let uu___10 =
                                                FStar_Ident.range_of_lid
                                                  (FStar_Syntax_Util.comp_effect_name
                                                     c1) in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                  "Constructors cannot have effects")
                                                uu___10)))
                             | uu___5 -> ([], t2) in
                           (match uu___3 with
                            | (arguments, result) ->
                                ((let uu___5 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low in
                                  if uu___5
                                  then
                                    let uu___6 =
                                      FStar_Syntax_Print.lid_to_string c in
                                    let uu___7 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments in
                                    let uu___8 =
                                      FStar_Syntax_Print.term_to_string
                                        result in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu___6 uu___7 uu___8
                                  else ());
                                 (let uu___5 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments in
                                  match uu___5 with
                                  | (arguments1, env', us) ->
                                      let type_u_tc =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_type u_tc)
                                          result.FStar_Syntax_Syntax.pos in
                                      let env'1 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          env' type_u_tc in
                                      let uu___6 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result in
                                      (match uu___6 with
                                       | (result1, res_lcomp) ->
                                           let uu___7 =
                                             FStar_Syntax_Util.head_and_args_full
                                               result1 in
                                           (match uu___7 with
                                            | (head, args) ->
                                                (FStar_Errors.stop_if_err ();
                                                 (let p_args =
                                                    let uu___9 =
                                                      FStar_Util.first_N
                                                        (FStar_List.length
                                                           tps) args in
                                                    FStar_Pervasives_Native.fst
                                                      uu___9 in
                                                  FStar_List.iter2
                                                    (fun uu___10 ->
                                                       fun uu___11 ->
                                                         match (uu___10,
                                                                 uu___11)
                                                         with
                                                         | ({
                                                              FStar_Syntax_Syntax.binder_bv
                                                                = bv;
                                                              FStar_Syntax_Syntax.binder_qual
                                                                = uu___12;
                                                              FStar_Syntax_Syntax.binder_attrs
                                                                = uu___13;_},
                                                            (t2, uu___14)) ->
                                                             let uu___15 =
                                                               let uu___16 =
                                                                 FStar_Syntax_Subst.compress
                                                                   t2 in
                                                               uu___16.FStar_Syntax_Syntax.n in
                                                             (match uu___15
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_name
                                                                  bv' when
                                                                  FStar_Syntax_Syntax.bv_eq
                                                                    bv bv'
                                                                  -> ()
                                                              | uu___16 ->
                                                                  let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv in
                                                                    let uu___20
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu___19
                                                                    uu___20 in
                                                                    (FStar_Errors.Error_BadInductiveParam,
                                                                    uu___18) in
                                                                  FStar_Errors.raise_error
                                                                    uu___17
                                                                    t2.FStar_Syntax_Syntax.pos))
                                                    tps p_args;
                                                  (let ty =
                                                     let uu___10 =
                                                       unfold_whnf env2
                                                         res_lcomp.FStar_TypeChecker_Common.res_typ in
                                                     FStar_All.pipe_right
                                                       uu___10
                                                       FStar_Syntax_Util.unrefine in
                                                   (let uu___11 =
                                                      let uu___12 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu___12.FStar_Syntax_Syntax.n in
                                                    match uu___11 with
                                                    | FStar_Syntax_Syntax.Tm_type
                                                        uu___12 -> ()
                                                    | uu___12 ->
                                                        let uu___13 =
                                                          let uu___14 =
                                                            let uu___15 =
                                                              FStar_Syntax_Print.term_to_string
                                                                result1 in
                                                            let uu___16 =
                                                              FStar_Syntax_Print.term_to_string
                                                                ty in
                                                            FStar_Util.format2
                                                              "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                              uu___15 uu___16 in
                                                          (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                            uu___14) in
                                                        FStar_Errors.raise_error
                                                          uu___13
                                                          se.FStar_Syntax_Syntax.sigrng);
                                                   (let g_uvs =
                                                      let uu___11 =
                                                        let uu___12 =
                                                          FStar_Syntax_Subst.compress
                                                            head in
                                                        uu___12.FStar_Syntax_Syntax.n in
                                                      match uu___11 with
                                                      | FStar_Syntax_Syntax.Tm_uinst
                                                          ({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_fvar
                                                               fv;
                                                             FStar_Syntax_Syntax.pos
                                                               = uu___12;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu___13;_},
                                                           tuvs)
                                                          when
                                                          FStar_Syntax_Syntax.fv_eq_lid
                                                            fv tc_lid
                                                          ->
                                                          if
                                                            (FStar_List.length
                                                               _uvs1)
                                                              =
                                                              (FStar_List.length
                                                                 tuvs)
                                                          then
                                                            FStar_List.fold_left2
                                                              (fun g ->
                                                                 fun u1 ->
                                                                   fun u2 ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Range.dummyRange in
                                                                    let uu___16
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Range.dummyRange in
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env'1
                                                                    uu___15
                                                                    uu___16 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g uu___14)
                                                              FStar_TypeChecker_Env.trivial_guard
                                                              tuvs _uvs1
                                                          else
                                                            FStar_Errors.raise_error
                                                              (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                                "Length of annotated universes does not match inferred universes")
                                                              se.FStar_Syntax_Syntax.sigrng
                                                      | FStar_Syntax_Syntax.Tm_fvar
                                                          fv when
                                                          FStar_Syntax_Syntax.fv_eq_lid
                                                            fv tc_lid
                                                          ->
                                                          FStar_TypeChecker_Env.trivial_guard
                                                      | uu___12 ->
                                                          let uu___13 =
                                                            let uu___14 =
                                                              let uu___15 =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  tc_lid in
                                                              let uu___16 =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head in
                                                              FStar_Util.format2
                                                                "Expected a constructor of type %s; got %s"
                                                                uu___15
                                                                uu___16 in
                                                            (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                              uu___14) in
                                                          FStar_Errors.raise_error
                                                            uu___13
                                                            se.FStar_Syntax_Syntax.sigrng in
                                                    let g =
                                                      FStar_List.fold_left2
                                                        (fun g1 ->
                                                           fun uu___11 ->
                                                             fun u_x ->
                                                               match uu___11
                                                               with
                                                               | {
                                                                   FStar_Syntax_Syntax.binder_bv
                                                                    = x;
                                                                   FStar_Syntax_Syntax.binder_qual
                                                                    = uu___12;
                                                                   FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___13;_}
                                                                   ->
                                                                   let uu___14
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc in
                                                                   FStar_TypeChecker_Env.conj_guard
                                                                    g1
                                                                    uu___14)
                                                        g_uvs arguments1 us in
                                                    let t2 =
                                                      let uu___11 =
                                                        let uu___12 =
                                                          FStar_All.pipe_right
                                                            tps
                                                            (FStar_List.map
                                                               (fun b ->
                                                                  let uu___13
                                                                    = b in
                                                                  {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    =
                                                                    (uu___13.FStar_Syntax_Syntax.binder_bv);
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true));
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    =
                                                                    (uu___13.FStar_Syntax_Syntax.binder_attrs)
                                                                  })) in
                                                        FStar_List.append
                                                          uu___12 arguments1 in
                                                      let uu___12 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          result1 in
                                                      FStar_Syntax_Util.arrow
                                                        uu___11 uu___12 in
                                                    let t3 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        _uvs1 t2 in
                                                    ((let uu___11 = se in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (c, _uvs1, t3,
                                                               tc_lid, ntps,
                                                               mutual_tcs));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___11.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___11.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___11.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___11.FStar_Syntax_Syntax.sigattrs);
                                                        FStar_Syntax_Syntax.sigopts
                                                          =
                                                          (uu___11.FStar_Syntax_Syntax.sigopts)
                                                      }), g)))))))))))))
        | uu___ -> failwith "impossible"
let (generalize_and_inst_within :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
          Prims.list))
  =
  fun env ->
    fun tcs ->
      fun datas ->
        let binders =
          FStar_All.pipe_right tcs
            (FStar_List.map
               (fun uu___ ->
                  match uu___ with
                  | (se, uu___1) ->
                      (match se.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (uu___2, uu___3, tps, k, uu___4, uu___5) ->
                           let uu___6 =
                             let uu___7 = FStar_Syntax_Syntax.mk_Total k in
                             FStar_All.pipe_left
                               (FStar_Syntax_Util.arrow tps) uu___7 in
                           FStar_Syntax_Syntax.null_binder uu___6
                       | uu___2 -> failwith "Impossible"))) in
        let binders' =
          FStar_All.pipe_right datas
            (FStar_List.map
               (fun se ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu___, uu___1, t, uu___2, uu___3, uu___4) ->
                      FStar_Syntax_Syntax.null_binder t
                  | uu___ -> failwith "Impossible")) in
        let t =
          let uu___ = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
          FStar_Syntax_Util.arrow (FStar_List.append binders binders') uu___ in
        (let uu___1 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "GenUniverses") in
         if uu___1
         then
           let uu___2 = FStar_TypeChecker_Normalize.term_to_string env t in
           FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n"
             uu___2
         else ());
        (let uu___1 = FStar_TypeChecker_Generalize.generalize_universes env t in
         match uu___1 with
         | (uvs, t1) ->
             ((let uu___3 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "GenUniverses") in
               if uu___3
               then
                 let uu___4 =
                   let uu___5 =
                     FStar_All.pipe_right uvs
                       (FStar_List.map (fun u -> FStar_Ident.string_of_id u)) in
                   FStar_All.pipe_right uu___5 (FStar_String.concat ", ") in
                 let uu___5 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" uu___4
                   uu___5
               else ());
              (let uu___3 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
               match uu___3 with
               | (uvs1, t2) ->
                   let uu___4 = FStar_Syntax_Util.arrow_formals t2 in
                   (match uu___4 with
                    | (args, uu___5) ->
                        let uu___6 =
                          FStar_Util.first_N (FStar_List.length binders) args in
                        (match uu___6 with
                         | (tc_types, data_types) ->
                             let tcs1 =
                               FStar_List.map2
                                 (fun uu___7 ->
                                    fun uu___8 ->
                                      match (uu___7, uu___8) with
                                      | ({ FStar_Syntax_Syntax.binder_bv = x;
                                           FStar_Syntax_Syntax.binder_qual =
                                             uu___9;
                                           FStar_Syntax_Syntax.binder_attrs =
                                             uu___10;_},
                                         (se, uu___11)) ->
                                          (match se.FStar_Syntax_Syntax.sigel
                                           with
                                           | FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc, uu___12, tps, uu___13,
                                                mutuals, datas1)
                                               ->
                                               let ty =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs1
                                                   x.FStar_Syntax_Syntax.sort in
                                               let uu___14 =
                                                 let uu___15 =
                                                   let uu___16 =
                                                     FStar_Syntax_Subst.compress
                                                       ty in
                                                   uu___16.FStar_Syntax_Syntax.n in
                                                 match uu___15 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (binders1, c) ->
                                                     let uu___16 =
                                                       FStar_Util.first_N
                                                         (FStar_List.length
                                                            tps) binders1 in
                                                     (match uu___16 with
                                                      | (tps1, rest) ->
                                                          let t3 =
                                                            match rest with
                                                            | [] ->
                                                                FStar_Syntax_Util.comp_result
                                                                  c
                                                            | uu___17 ->
                                                                FStar_Syntax_Syntax.mk
                                                                  (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                  (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                          (tps1, t3))
                                                 | uu___16 -> ([], ty) in
                                               (match uu___14 with
                                                | (tps1, t3) ->
                                                    let uu___15 = se in
                                                    {
                                                      FStar_Syntax_Syntax.sigel
                                                        =
                                                        (FStar_Syntax_Syntax.Sig_inductive_typ
                                                           (tc, uvs1, tps1,
                                                             t3, mutuals,
                                                             datas1));
                                                      FStar_Syntax_Syntax.sigrng
                                                        =
                                                        (uu___15.FStar_Syntax_Syntax.sigrng);
                                                      FStar_Syntax_Syntax.sigquals
                                                        =
                                                        (uu___15.FStar_Syntax_Syntax.sigquals);
                                                      FStar_Syntax_Syntax.sigmeta
                                                        =
                                                        (uu___15.FStar_Syntax_Syntax.sigmeta);
                                                      FStar_Syntax_Syntax.sigattrs
                                                        =
                                                        (uu___15.FStar_Syntax_Syntax.sigattrs);
                                                      FStar_Syntax_Syntax.sigopts
                                                        =
                                                        (uu___15.FStar_Syntax_Syntax.sigopts)
                                                    })
                                           | uu___12 -> failwith "Impossible"))
                                 tc_types tcs in
                             let datas1 =
                               match uvs1 with
                               | [] -> datas
                               | uu___7 ->
                                   let uvs_universes =
                                     FStar_All.pipe_right uvs1
                                       (FStar_List.map
                                          (fun uu___8 ->
                                             FStar_Syntax_Syntax.U_name
                                               uu___8)) in
                                   let tc_insts =
                                     FStar_All.pipe_right tcs1
                                       (FStar_List.map
                                          (fun uu___8 ->
                                             match uu___8 with
                                             | {
                                                 FStar_Syntax_Syntax.sigel =
                                                   FStar_Syntax_Syntax.Sig_inductive_typ
                                                   (tc, uu___9, uu___10,
                                                    uu___11, uu___12,
                                                    uu___13);
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu___14;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = uu___15;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   = uu___16;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = uu___17;
                                                 FStar_Syntax_Syntax.sigopts
                                                   = uu___18;_}
                                                 -> (tc, uvs_universes)
                                             | uu___9 ->
                                                 failwith "Impossible")) in
                                   FStar_List.map2
                                     (fun uu___8 ->
                                        fun d ->
                                          match uu___8 with
                                          | {
                                              FStar_Syntax_Syntax.binder_bv =
                                                t3;
                                              FStar_Syntax_Syntax.binder_qual
                                                = uu___9;
                                              FStar_Syntax_Syntax.binder_attrs
                                                = uu___10;_}
                                              ->
                                              (match d.FStar_Syntax_Syntax.sigel
                                               with
                                               | FStar_Syntax_Syntax.Sig_datacon
                                                   (l, uu___11, uu___12, tc,
                                                    ntps, mutuals)
                                                   ->
                                                   let ty =
                                                     let uu___13 =
                                                       FStar_Syntax_InstFV.instantiate
                                                         tc_insts
                                                         t3.FStar_Syntax_Syntax.sort in
                                                     FStar_All.pipe_right
                                                       uu___13
                                                       (FStar_Syntax_Subst.close_univ_vars
                                                          uvs1) in
                                                   let uu___13 = d in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (l, uvs1, ty, tc,
                                                            ntps, mutuals));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___13.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___13.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___13.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___13.FStar_Syntax_Syntax.sigattrs);
                                                     FStar_Syntax_Syntax.sigopts
                                                       =
                                                       (uu___13.FStar_Syntax_Syntax.sigopts)
                                                   }
                                               | uu___11 ->
                                                   failwith "Impossible"))
                                     data_types datas in
                             (tcs1, datas1))))))
let (debug_log :
  FStar_TypeChecker_Env.env_t -> (unit -> Prims.string) -> unit) =
  fun env ->
    fun msg ->
      let uu___ =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu___
      then
        let uu___1 =
          let uu___2 = let uu___3 = msg () in Prims.op_Hat uu___3 "\n" in
          Prims.op_Hat "Positivity::" uu___2 in
        FStar_Util.print_string uu___1
      else ()
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid ->
    fun t ->
      let uu___ = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu___
let rec (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_name uu___1 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Pervasives_Native.Some (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress t1 in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Pervasives_Native.Some (fv, us)
         | uu___2 ->
             failwith
               "try_get_fv: Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu___1, uu___2) -> try_get_fv t1
    | uu___1 ->
        let uu___2 =
          let uu___3 = FStar_Syntax_Print.tag_of_term t in
          Prims.op_Hat "try_get_fv: did not expect t to be a : " uu___3 in
        failwith uu___2
type unfolded_memo_elt =
  (FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list
type unfolded_memo_t = unfolded_memo_elt FStar_ST.ref
let (already_unfolded :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ilid ->
    fun arrghs ->
      fun unfolded ->
        fun env ->
          let uu___ = FStar_ST.op_Bang unfolded in
          FStar_List.existsML
            (fun uu___1 ->
               match uu___1 with
               | (lid, l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu___2 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu___2 in
                      FStar_List.fold_left2
                        (fun b ->
                           fun a ->
                             fun a' ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu___
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid ->
    fun btype ->
      fun unfolded ->
        fun env ->
          debug_log env
            (fun uu___1 ->
               let uu___2 = FStar_Syntax_Print.term_to_string btype in
               Prims.op_Hat "Checking strict positivity in type: " uu___2);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.HNF;
               FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.Iota;
               FStar_TypeChecker_Env.ForExtraction;
               FStar_TypeChecker_Env.Unascribe;
               FStar_TypeChecker_Env.AllowUnboundUniverses] env btype in
           debug_log env
             (fun uu___2 ->
                let uu___3 = FStar_Syntax_Print.term_to_string btype1 in
                Prims.op_Hat
                  "Checking strict positivity in type, after normalization: "
                  uu___3);
           (let uu___2 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu___2) ||
             ((debug_log env
                 (fun uu___3 -> "ty does occur in this type, pressing ahead");
               (let uu___3 =
                  let uu___4 = FStar_Syntax_Subst.compress btype1 in
                  uu___4.FStar_Syntax_Syntax.n in
                match uu___3 with
                | FStar_Syntax_Syntax.Tm_app (t, args) ->
                    let fv_us_opt = try_get_fv t in
                    let uu___4 =
                      FStar_All.pipe_right fv_us_opt FStar_Util.is_none in
                    if uu___4
                    then true
                    else
                      (let uu___6 =
                         FStar_All.pipe_right fv_us_opt FStar_Util.must in
                       match uu___6 with
                       | (fv, us) ->
                           let uu___7 =
                             FStar_Ident.lid_equals
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               ty_lid in
                           if uu___7
                           then
                             (debug_log env
                                (fun uu___9 ->
                                   "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
                              FStar_List.for_all
                                (fun uu___9 ->
                                   match uu___9 with
                                   | (t1, uu___10) ->
                                       let uu___11 = ty_occurs_in ty_lid t1 in
                                       Prims.op_Negation uu___11) args)
                           else
                             (debug_log env
                                (fun uu___10 ->
                                   "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
                              ty_nested_positive_in_inductive ty_lid
                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                    (debug_log env
                       (fun uu___5 ->
                          "Checking strict positivity in Tm_arrow");
                     (let check_comp =
                        let c1 =
                          let uu___5 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                          FStar_All.pipe_right uu___5
                            FStar_Syntax_Syntax.mk_Comp in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu___5 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1) in
                           FStar_All.pipe_right uu___5
                             (FStar_List.existsb
                                (fun q -> q = FStar_Syntax_Syntax.TotalEffect))) in
                      if Prims.op_Negation check_comp
                      then
                        (debug_log env
                           (fun uu___6 ->
                              "Checking strict positivity , the arrow is impure, so return true");
                         true)
                      else
                        (debug_log env
                           (fun uu___7 ->
                              "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
                         (FStar_List.for_all
                            (fun uu___7 ->
                               match uu___7 with
                               | { FStar_Syntax_Syntax.binder_bv = b;
                                   FStar_Syntax_Syntax.binder_qual = uu___8;
                                   FStar_Syntax_Syntax.binder_attrs = uu___9;_}
                                   ->
                                   let uu___10 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu___10) sbs)
                           &&
                           ((let uu___7 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu___7 with
                             | (uu___8, return_type) ->
                                 let uu___9 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu___9)))))
                | FStar_Syntax_Syntax.Tm_fvar uu___4 ->
                    (debug_log env
                       (fun uu___6 ->
                          "Checking strict positivity in an fvar, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_type uu___4 ->
                    (debug_log env
                       (fun uu___6 ->
                          "Checking strict positivity in an Tm_type, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t, uu___4) ->
                    (debug_log env
                       (fun uu___6 ->
                          "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv, uu___4) ->
                    (debug_log env
                       (fun uu___6 ->
                          "Checking strict positivity in an Tm_refine, recur in the bv sort)");
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu___4, uu___5, branches) ->
                    (debug_log env
                       (fun uu___7 ->
                          "Checking strict positivity in an Tm_match, recur in the branches)");
                     FStar_List.for_all
                       (fun uu___7 ->
                          match uu___7 with
                          | (p, uu___8, t) ->
                              let bs =
                                let uu___9 = FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu___9 in
                              let uu___9 = FStar_Syntax_Subst.open_term bs t in
                              (match uu___9 with
                               | (bs1, t1) ->
                                   let uu___10 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu___10)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t, uu___4, uu___5) ->
                    (debug_log env
                       (fun uu___7 ->
                          "Checking strict positivity in an Tm_ascribed, recur)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu___4 ->
                    (debug_log env
                       (fun uu___6 ->
                          let uu___7 =
                            let uu___8 =
                              FStar_Syntax_Print.tag_of_term btype1 in
                            let uu___9 =
                              let uu___10 =
                                FStar_Syntax_Print.term_to_string btype1 in
                              Prims.op_Hat " and term: " uu___10 in
                            Prims.op_Hat uu___8 uu___9 in
                          Prims.op_Hat
                            "Checking strict positivity, unexpected tag: "
                            uu___7);
                     false)))))
and (ty_nested_positive_in_inductive :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universes ->
        FStar_Syntax_Syntax.args ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid ->
    fun ilid ->
      fun us ->
        fun args ->
          fun unfolded ->
            fun env ->
              debug_log env
                (fun uu___1 ->
                   let uu___2 =
                     let uu___3 = FStar_Ident.string_of_lid ilid in
                     let uu___4 =
                       let uu___5 = FStar_Syntax_Print.args_to_string args in
                       Prims.op_Hat " applied to arguments: " uu___5 in
                     Prims.op_Hat uu___3 uu___4 in
                   Prims.op_Hat
                     "Checking nested positivity in the inductive " uu___2);
              (let uu___1 = FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu___1 with
               | (b, idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu___2 =
                       let uu___3 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None in
                       FStar_TypeChecker_Env.fv_has_attr env uu___3
                         FStar_Parser_Const.assume_strictly_positive_attr_lid in
                     (if uu___2
                      then
                        (debug_log env
                           (fun uu___4 ->
                              let uu___5 = FStar_Ident.string_of_lid ilid in
                              FStar_Util.format1
                                "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                                uu___5);
                         true)
                      else
                        (debug_log env
                           (fun uu___5 ->
                              "Checking nested positivity, not an inductive, return false");
                         false))
                   else
                     (let uu___3 = already_unfolded ilid args unfolded env in
                      if uu___3
                      then
                        (debug_log env
                           (fun uu___5 ->
                              "Checking nested positivity, we have already unfolded this inductive with these args");
                         true)
                      else
                        (let num_ibs =
                           let uu___5 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid in
                           FStar_Option.get uu___5 in
                         debug_log env
                           (fun uu___6 ->
                              let uu___7 =
                                let uu___8 = FStar_Util.string_of_int num_ibs in
                                Prims.op_Hat uu___8
                                  ", also adding to the memo table" in
                              Prims.op_Hat
                                "Checking nested positivity, number of type parameters is "
                                uu___7);
                         (let uu___7 =
                            let uu___8 = FStar_ST.op_Bang unfolded in
                            let uu___9 =
                              let uu___10 =
                                let uu___11 =
                                  let uu___12 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu___12 in
                                (ilid, uu___11) in
                              [uu___10] in
                            FStar_List.append uu___8 uu___9 in
                          FStar_ST.op_Colon_Equals unfolded uu___7);
                         FStar_List.for_all
                           (fun d ->
                              ty_nested_positive_in_dlid ty_lid d ilid us
                                args num_ibs unfolded env) idatas)))
and (ty_nested_positive_in_dlid :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            Prims.int ->
              unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid ->
    fun dlid ->
      fun ilid ->
        fun us ->
          fun args ->
            fun num_ibs ->
              fun unfolded ->
                fun env ->
                  debug_log env
                    (fun uu___1 ->
                       let uu___2 =
                         let uu___3 = FStar_Ident.string_of_lid dlid in
                         let uu___4 =
                           let uu___5 = FStar_Ident.string_of_lid ilid in
                           Prims.op_Hat " of the inductive " uu___5 in
                         Prims.op_Hat uu___3 uu___4 in
                       Prims.op_Hat
                         "Checking nested positivity in data constructor "
                         uu___2);
                  (let uu___1 = FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu___1 with
                   | (univ_unif_vars, dt) ->
                       (FStar_List.iter2
                          (fun u' ->
                             fun u ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu___3 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us;
                        debug_log env
                          (fun uu___4 ->
                             let uu___5 =
                               FStar_Syntax_Print.term_to_string dt in
                             Prims.op_Hat
                               "Checking nested positivity in the data constructor type: "
                               uu___5);
                        (let uu___4 =
                           let uu___5 = FStar_Syntax_Subst.compress dt in
                           uu___5.FStar_Syntax_Syntax.n in
                         match uu___4 with
                         | FStar_Syntax_Syntax.Tm_arrow (dbs, c) ->
                             (debug_log env
                                (fun uu___6 ->
                                   "Checked nested positivity in Tm_arrow data constructor type");
                              (let uu___6 = FStar_List.splitAt num_ibs dbs in
                               match uu___6 with
                               | (ibs, dbs1) ->
                                   let ibs1 =
                                     FStar_Syntax_Subst.open_binders ibs in
                                   let dbs2 =
                                     let uu___7 =
                                       FStar_Syntax_Subst.opening_of_binders
                                         ibs1 in
                                     FStar_Syntax_Subst.subst_binders uu___7
                                       dbs1 in
                                   let c1 =
                                     let uu___7 =
                                       FStar_Syntax_Subst.opening_of_binders
                                         ibs1 in
                                     FStar_Syntax_Subst.subst_comp uu___7 c in
                                   let uu___7 =
                                     FStar_List.splitAt num_ibs args in
                                   (match uu___7 with
                                    | (args1, uu___8) ->
                                        let subst =
                                          FStar_List.fold_left2
                                            (fun subst1 ->
                                               fun ib ->
                                                 fun arg ->
                                                   FStar_List.append subst1
                                                     [FStar_Syntax_Syntax.NT
                                                        ((ib.FStar_Syntax_Syntax.binder_bv),
                                                          (FStar_Pervasives_Native.fst
                                                             arg))]) [] ibs1
                                            args1 in
                                        let dbs3 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst dbs2 in
                                        let c2 =
                                          let uu___9 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length dbs3) subst in
                                          FStar_Syntax_Subst.subst_comp
                                            uu___9 c1 in
                                        (debug_log env
                                           (fun uu___10 ->
                                              let uu___11 =
                                                let uu___12 =
                                                  FStar_Syntax_Print.binders_to_string
                                                    "; " dbs3 in
                                                let uu___13 =
                                                  let uu___14 =
                                                    FStar_Syntax_Print.comp_to_string
                                                      c2 in
                                                  Prims.op_Hat ", and c: "
                                                    uu___14 in
                                                Prims.op_Hat uu___12 uu___13 in
                                              Prims.op_Hat
                                                "Checking nested positivity in the unfolded data constructor binders as: "
                                                uu___11);
                                         ty_nested_positive_in_type ty_lid
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (dbs3, c2)) ilid num_ibs
                                           unfolded env))))
                         | uu___5 ->
                             (debug_log env
                                (fun uu___7 ->
                                   "Checking nested positivity in the data constructor type that is not an arrow");
                              (let uu___7 =
                                 let uu___8 = FStar_Syntax_Subst.compress dt in
                                 uu___8.FStar_Syntax_Syntax.n in
                               ty_nested_positive_in_type ty_lid uu___7 ilid
                                 num_ibs unfolded env)))))
and (ty_nested_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' ->
      FStar_Ident.lident ->
        Prims.int ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid ->
    fun t ->
      fun ilid ->
        fun num_ibs ->
          fun unfolded ->
            fun env ->
              match t with
              | FStar_Syntax_Syntax.Tm_app (t1, args) ->
                  (debug_log env
                     (fun uu___1 ->
                        "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself");
                   (let uu___1 =
                      let uu___2 = try_get_fv t1 in
                      FStar_All.pipe_right uu___2 FStar_Util.must in
                    match uu___1 with
                    | (fv, uu___2) ->
                        let uu___3 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid in
                        if uu___3
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                  (debug_log env
                     (fun uu___1 ->
                        let uu___2 =
                          FStar_Syntax_Print.binders_to_string "; " sbs in
                        Prims.op_Hat
                          "Checking nested positivity in an Tm_arrow node, with binders as: "
                          uu___2);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu___1 =
                      FStar_List.fold_left
                        (fun uu___2 ->
                           fun b ->
                             match uu___2 with
                             | (r, env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu___4 =
                                      ty_strictly_positive_in_type ty_lid
                                        (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu___5 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu___4, uu___5))) (true, env) sbs1 in
                    match uu___1 with | (b, uu___2) -> b))
              | uu___ -> failwith "Nested positive check, unhandled case"
let (ty_positive_in_datacon :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.universes ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env -> Prims.bool)
  =
  fun ty_lid ->
    fun dlid ->
      fun ty_bs ->
        fun us ->
          fun unfolded ->
            fun env ->
              let uu___ = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu___ with
              | (univ_unif_vars, dt) ->
                  (FStar_List.iter2
                     (fun u' ->
                        fun u ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu___2 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   debug_log env
                     (fun uu___3 ->
                        let uu___4 = FStar_Syntax_Print.term_to_string dt in
                        Prims.op_Hat "Checking data constructor type: "
                          uu___4);
                   (let uu___3 =
                      let uu___4 = FStar_Syntax_Subst.compress dt in
                      uu___4.FStar_Syntax_Syntax.n in
                    match uu___3 with
                    | FStar_Syntax_Syntax.Tm_fvar uu___4 ->
                        (debug_log env
                           (fun uu___6 ->
                              "Data constructor type is simply an fvar, returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs, uu___4) ->
                        let dbs1 =
                          let uu___5 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu___5 in
                        let dbs2 =
                          let uu___5 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu___5 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        (debug_log env
                           (fun uu___6 ->
                              let uu___7 =
                                let uu___8 =
                                  FStar_Util.string_of_int
                                    (FStar_List.length dbs3) in
                                Prims.op_Hat uu___8 " binders" in
                              Prims.op_Hat
                                "Data constructor type is an arrow type, so checking strict positivity in "
                                uu___7);
                         (let uu___6 =
                            FStar_List.fold_left
                              (fun uu___7 ->
                                 fun b ->
                                   match uu___7 with
                                   | (r, env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu___9 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu___10 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu___9, uu___10))) (true, env)
                              dbs3 in
                          match uu___6 with | (b, uu___7) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu___4, uu___5) ->
                        (debug_log env
                           (fun uu___7 ->
                              "Data constructor type is a Tm_app, so returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t, univs) ->
                        (debug_log env
                           (fun uu___5 ->
                              "Data constructor type is a Tm_uinst, so recursing in the base type");
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu___4 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty ->
    fun env ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu___ =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, us, bs, uu___1, uu___2, uu___3) -> (lid, us, bs)
        | uu___1 -> failwith "Impossible!" in
      match uu___ with
      | (ty_lid, ty_us, ty_bs) ->
          let uu___1 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu___1 with
           | (ty_usubst, ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu___2 =
                 let uu___3 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu___3 in
               FStar_List.for_all
                 (fun d ->
                    let uu___3 =
                      FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu___3
                      unfolded_inductives env2) uu___2)
let (check_exn_positivity :
  FStar_Ident.lid -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun data_ctor_lid ->
    fun env ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      ty_positive_in_datacon FStar_Parser_Const.exn_lid data_ctor_lid [] []
        unfolded_inductives env
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu___, uu___1, t, uu___2, uu___3, uu___4) -> t
    | uu___ -> failwith "Impossible!"
let (haseq_suffix : Prims.string) = "__uu___haseq"
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid ->
    let str = FStar_Ident.string_of_lid lid in
    let len = FStar_String.length str in
    let haseq_suffix_len = FStar_String.length haseq_suffix in
    (len > haseq_suffix_len) &&
      (let uu___ =
         let uu___1 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len in
         FStar_String.compare uu___1 haseq_suffix in
       uu___ = Prims.int_zero)
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid ->
    let uu___ =
      let uu___1 = FStar_Ident.ns_of_lid lid in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 = FStar_Ident.ident_of_lid lid in
              FStar_Ident.string_of_id uu___6 in
            Prims.op_Hat uu___5 haseq_suffix in
          FStar_Ident.id_of_text uu___4 in
        [uu___3] in
      FStar_List.append uu___1 uu___2 in
    FStar_Ident.lid_of_ids uu___
let (get_optimized_haseq_axiom :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_names ->
          (FStar_Ident.lident * FStar_Syntax_Syntax.term *
            FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders *
            FStar_Syntax_Syntax.term))
  =
  fun en ->
    fun ty ->
      fun usubst ->
        fun us ->
          let uu___ =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, uu___1, bs, t, uu___2, uu___3) -> (lid, bs, t)
            | uu___1 -> failwith "Impossible!" in
          match uu___ with
          | (lid, bs, t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
              let t1 =
                let uu___1 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst in
                FStar_Syntax_Subst.subst uu___1 t in
              let uu___1 = FStar_Syntax_Subst.open_term bs1 t1 in
              (match uu___1 with
               | (bs2, t2) ->
                   let ibs =
                     let uu___2 =
                       let uu___3 = FStar_Syntax_Subst.compress t2 in
                       uu___3.FStar_Syntax_Syntax.n in
                     match uu___2 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs1, uu___3) -> ibs1
                     | uu___3 -> [] in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                   let ind =
                     let uu___2 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None in
                     let uu___3 =
                       FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name u)
                         us in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu___2 uu___3 in
                   let ind1 =
                     let uu___2 =
                       FStar_List.map
                         (fun uu___3 ->
                            match uu___3 with
                            | { FStar_Syntax_Syntax.binder_bv = bv;
                                FStar_Syntax_Syntax.binder_qual = aq;
                                FStar_Syntax_Syntax.binder_attrs = uu___4;_}
                                ->
                                let uu___5 =
                                  FStar_Syntax_Syntax.bv_to_name bv in
                                (uu___5, aq)) bs2 in
                     FStar_Syntax_Syntax.mk_Tm_app ind uu___2
                       FStar_Range.dummyRange in
                   let ind2 =
                     let uu___2 =
                       FStar_List.map
                         (fun uu___3 ->
                            match uu___3 with
                            | { FStar_Syntax_Syntax.binder_bv = bv;
                                FStar_Syntax_Syntax.binder_qual = aq;
                                FStar_Syntax_Syntax.binder_attrs = uu___4;_}
                                ->
                                let uu___5 =
                                  FStar_Syntax_Syntax.bv_to_name bv in
                                (uu___5, aq)) ibs1 in
                     FStar_Syntax_Syntax.mk_Tm_app ind1 uu___2
                       FStar_Range.dummyRange in
                   let haseq_ind =
                     let uu___2 =
                       let uu___3 = FStar_Syntax_Syntax.as_arg ind2 in
                       [uu___3] in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                       uu___2 FStar_Range.dummyRange in
                   let bs' =
                     FStar_List.filter
                       (fun b ->
                          let uu___2 =
                            let uu___3 = FStar_Syntax_Util.type_u () in
                            FStar_Pervasives_Native.fst uu___3 in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                            uu___2) bs2 in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3 ->
                          fun b ->
                            let uu___2 =
                              let uu___3 =
                                let uu___4 =
                                  let uu___5 =
                                    FStar_Syntax_Syntax.bv_to_name
                                      b.FStar_Syntax_Syntax.binder_bv in
                                  FStar_Syntax_Syntax.as_arg uu___5 in
                                [uu___4] in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.t_haseq uu___3
                                FStar_Range.dummyRange in
                            FStar_Syntax_Util.mk_conj t3 uu___2)
                       FStar_Syntax_Util.t_true bs' in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
                   let fml1 =
                     let uu___2 = fml in
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           let uu___6 =
                             let uu___7 =
                               FStar_Syntax_Syntax.binders_to_names ibs1 in
                             let uu___8 =
                               let uu___9 =
                                 let uu___10 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind in
                                 [uu___10] in
                               [uu___9] in
                             (uu___7, uu___8) in
                           FStar_Syntax_Syntax.Meta_pattern uu___6 in
                         (fml, uu___5) in
                       FStar_Syntax_Syntax.Tm_meta uu___4 in
                     {
                       FStar_Syntax_Syntax.n = uu___3;
                       FStar_Syntax_Syntax.pos =
                         (uu___2.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___2.FStar_Syntax_Syntax.vars)
                     } in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu___2 =
                              let uu___3 =
                                let uu___4 =
                                  let uu___5 =
                                    let uu___6 =
                                      FStar_Syntax_Syntax.mk_binder
                                        b.FStar_Syntax_Syntax.binder_bv in
                                    [uu___6] in
                                  let uu___6 =
                                    FStar_Syntax_Subst.close [b] t3 in
                                  FStar_Syntax_Util.abs uu___5 uu___6
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.as_arg uu___4 in
                              [uu___3] in
                            FStar_Syntax_Syntax.mk_Tm_app
                              FStar_Syntax_Util.tforall uu___2
                              FStar_Range.dummyRange) ibs1 fml1 in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu___2 =
                              let uu___3 =
                                let uu___4 =
                                  let uu___5 =
                                    let uu___6 =
                                      FStar_Syntax_Syntax.mk_binder
                                        b.FStar_Syntax_Syntax.binder_bv in
                                    [uu___6] in
                                  let uu___6 =
                                    FStar_Syntax_Subst.close [b] t3 in
                                  FStar_Syntax_Util.abs uu___5 uu___6
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.as_arg uu___4 in
                              [uu___3] in
                            FStar_Syntax_Syntax.mk_Tm_app
                              FStar_Syntax_Util.tforall uu___2
                              FStar_Range.dummyRange) bs2 fml2 in
                   let axiom_lid = get_haseq_axiom_lid lid in
                   (axiom_lid, fml3, bs2, ibs1, haseq_bs))
let (optimized_haseq_soundness_for_data :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term)
  =
  fun ty_lid ->
    fun data ->
      fun usubst ->
        fun bs ->
          let dt = datacon_typ data in
          let dt1 = FStar_Syntax_Subst.subst usubst dt in
          let uu___ =
            let uu___1 = FStar_Syntax_Subst.compress dt1 in
            uu___1.FStar_Syntax_Syntax.n in
          match uu___ with
          | FStar_Syntax_Syntax.Tm_arrow (dbs, uu___1) ->
              let dbs1 =
                let uu___2 = FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu___2 in
              let dbs2 =
                let uu___2 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu___2 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t ->
                     fun b ->
                       let haseq_b =
                         let uu___2 =
                           let uu___3 =
                             FStar_Syntax_Syntax.as_arg
                               (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                           [uu___3] in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu___2
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu___2 =
                           let uu___3 = FStar_Ident.string_of_lid ty_lid in
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             uu___3 in
                         FStar_TypeChecker_Util.label uu___2 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b ->
                   fun t ->
                     let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             let uu___6 =
                               FStar_Syntax_Syntax.mk_binder
                                 b.FStar_Syntax_Syntax.binder_bv in
                             [uu___6] in
                           let uu___6 = FStar_Syntax_Subst.close [b] t in
                           FStar_Syntax_Util.abs uu___5 uu___6
                             FStar_Pervasives_Native.None in
                         FStar_Syntax_Syntax.as_arg uu___4 in
                       [uu___3] in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                       uu___2 FStar_Range.dummyRange) dbs3 cond
          | uu___1 -> FStar_Syntax_Util.t_true
let (optimized_haseq_ty :
  FStar_Syntax_Syntax.sigelts ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list *
          FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax) ->
          FStar_Syntax_Syntax.sigelt ->
            ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list *
              FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term'
              FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term'
              FStar_Syntax_Syntax.syntax))
  =
  fun all_datas_in_the_bundle ->
    fun usubst ->
      fun us ->
        fun acc ->
          fun ty ->
            let lid =
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid1, uu___, uu___1, uu___2, uu___3, uu___4) -> lid1
              | uu___ -> failwith "Impossible!" in
            let uu___ = acc in
            match uu___ with
            | (uu___1, en, uu___2, uu___3) ->
                let uu___4 = get_optimized_haseq_axiom en ty usubst us in
                (match uu___4 with
                 | (axiom_lid, fml, bs, ibs, haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml in
                     let uu___5 = acc in
                     (match uu___5 with
                      | (l_axioms, env, guard', cond') ->
                          let env1 =
                            FStar_TypeChecker_Env.push_binders env bs in
                          let env2 =
                            FStar_TypeChecker_Env.push_binders env1 ibs in
                          let t_datas =
                            FStar_List.filter
                              (fun s ->
                                 match s.FStar_Syntax_Syntax.sigel with
                                 | FStar_Syntax_Syntax.Sig_datacon
                                     (uu___6, uu___7, uu___8, t_lid, uu___9,
                                      uu___10)
                                     -> t_lid = lid
                                 | uu___6 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1 ->
                                 fun d ->
                                   let uu___6 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs in
                                   FStar_Syntax_Util.mk_conj acc1 uu___6)
                              FStar_Syntax_Util.t_true t_datas in
                          let uu___6 = FStar_Syntax_Util.mk_conj guard' guard in
                          let uu___7 = FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu___6, uu___7)))
let (optimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle ->
    fun tcs ->
      fun datas ->
        fun env0 ->
          let uu___ =
            let ty = FStar_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu___1, us, uu___2, t, uu___3, uu___4) -> (us, t)
            | uu___1 -> failwith "Impossible!" in
          match uu___ with
          | (us, t) ->
              let uu___1 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu___1 with
               | (usubst, us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     let uu___4 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs in
                     match uu___4 with
                     | (axioms, env2, guard, cond) ->
                         let phi =
                           let uu___5 = FStar_Syntax_Util.arrow_formals t in
                           match uu___5 with
                           | (uu___6, t1) ->
                               let uu___7 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1 in
                               if uu___7
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond in
                         let uu___5 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                         (match uu___5 with
                          | (phi1, uu___6) ->
                              ((let uu___8 =
                                  FStar_TypeChecker_Env.should_verify env2 in
                                if uu___8
                                then
                                  let uu___9 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1) in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu___9
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l ->
                                       fun uu___8 ->
                                         match uu___8 with
                                         | (lid, fml) ->
                                             let fml1 =
                                               FStar_Syntax_Subst.close_univ_vars
                                                 us1 fml in
                                             FStar_List.append l
                                               [{
                                                  FStar_Syntax_Syntax.sigel =
                                                    (FStar_Syntax_Syntax.Sig_assume
                                                       (lid, us1, fml1));
                                                  FStar_Syntax_Syntax.sigrng
                                                    = FStar_Range.dummyRange;
                                                  FStar_Syntax_Syntax.sigquals
                                                    = [];
                                                  FStar_Syntax_Syntax.sigmeta
                                                    =
                                                    FStar_Syntax_Syntax.default_sigmeta;
                                                  FStar_Syntax_Syntax.sigattrs
                                                    = [];
                                                  FStar_Syntax_Syntax.sigopts
                                                    =
                                                    FStar_Pervasives_Native.None
                                                }]) [] axioms in
                                (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                                  "haseq";
                                ses))))))
let (unoptimized_haseq_data :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lident Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun usubst ->
    fun bs ->
      fun haseq_ind ->
        fun mutuals ->
          fun acc ->
            fun data ->
              let rec is_mutual t =
                let uu___ =
                  let uu___1 = FStar_Syntax_Subst.compress t in
                  uu___1.FStar_Syntax_Syntax.n in
                match uu___ with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t', uu___1) -> is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv, t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t', args) ->
                    let uu___1 = is_mutual t' in
                    if uu___1
                    then true
                    else
                      (let uu___3 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu___3)
                | FStar_Syntax_Syntax.Tm_meta (t', uu___1) -> is_mutual t'
                | uu___1 -> false
              and exists_mutual uu___ =
                match uu___ with
                | [] -> false
                | hd::tl -> (is_mutual hd) || (exists_mutual tl) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu___ =
                let uu___1 = FStar_Syntax_Subst.compress dt1 in
                uu___1.FStar_Syntax_Syntax.n in
              match uu___ with
              | FStar_Syntax_Syntax.Tm_arrow (dbs, uu___1) ->
                  let dbs1 =
                    let uu___2 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu___2 in
                  let dbs2 =
                    let uu___2 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu___2 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t ->
                         fun b ->
                           let sort =
                             (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu___2 =
                               let uu___3 =
                                 FStar_Syntax_Syntax.as_arg
                                   (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                               [uu___3] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.t_haseq uu___2
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu___2 = is_mutual sort in
                             if uu___2
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b ->
                         fun t ->
                           let uu___2 =
                             let uu___3 =
                               let uu___4 =
                                 let uu___5 =
                                   let uu___6 =
                                     FStar_Syntax_Syntax.mk_binder
                                       b.FStar_Syntax_Syntax.binder_bv in
                                   [uu___6] in
                                 let uu___6 = FStar_Syntax_Subst.close [b] t in
                                 FStar_Syntax_Util.abs uu___5 uu___6
                                   FStar_Pervasives_Native.None in
                               FStar_Syntax_Syntax.as_arg uu___4 in
                             [uu___3] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.tforall uu___2
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu___1 -> acc
let (unoptimized_haseq_ty :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Ident.lident Prims.list ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_name Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun all_datas_in_the_bundle ->
    fun mutuals ->
      fun usubst ->
        fun us ->
          fun acc ->
            fun ty ->
              let uu___ =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid, uu___1, bs, t, uu___2, d_lids) ->
                    (lid, bs, t, d_lids)
                | uu___1 -> failwith "Impossible!" in
              match uu___ with
              | (lid, bs, t, d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu___1 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst in
                    FStar_Syntax_Subst.subst uu___1 t in
                  let uu___1 = FStar_Syntax_Subst.open_term bs1 t1 in
                  (match uu___1 with
                   | (bs2, t2) ->
                       let ibs =
                         let uu___2 =
                           let uu___3 = FStar_Syntax_Subst.compress t2 in
                           uu___3.FStar_Syntax_Syntax.n in
                         match uu___2 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs1, uu___3) ->
                             ibs1
                         | uu___3 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu___2 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         let uu___3 =
                           FStar_List.map
                             (fun u -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu___2 uu___3 in
                       let ind1 =
                         let uu___2 =
                           FStar_List.map
                             (fun uu___3 ->
                                match uu___3 with
                                | { FStar_Syntax_Syntax.binder_bv = bv;
                                    FStar_Syntax_Syntax.binder_qual = aq;
                                    FStar_Syntax_Syntax.binder_attrs = uu___4;_}
                                    ->
                                    let uu___5 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu___5, aq)) bs2 in
                         FStar_Syntax_Syntax.mk_Tm_app ind uu___2
                           FStar_Range.dummyRange in
                       let ind2 =
                         let uu___2 =
                           FStar_List.map
                             (fun uu___3 ->
                                match uu___3 with
                                | { FStar_Syntax_Syntax.binder_bv = bv;
                                    FStar_Syntax_Syntax.binder_qual = aq;
                                    FStar_Syntax_Syntax.binder_attrs = uu___4;_}
                                    ->
                                    let uu___5 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu___5, aq)) ibs1 in
                         FStar_Syntax_Syntax.mk_Tm_app ind1 uu___2
                           FStar_Range.dummyRange in
                       let haseq_ind =
                         let uu___2 =
                           let uu___3 = FStar_Syntax_Syntax.as_arg ind2 in
                           [uu___3] in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu___2
                           FStar_Range.dummyRange in
                       let t_datas =
                         FStar_List.filter
                           (fun s ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu___2, uu___3, uu___4, t_lid, uu___5,
                                   uu___6)
                                  -> t_lid = lid
                              | uu___2 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___2 = fml in
                         let uu___3 =
                           let uu___4 =
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1 in
                                 let uu___8 =
                                   let uu___9 =
                                     let uu___10 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind in
                                     [uu___10] in
                                   [uu___9] in
                                 (uu___7, uu___8) in
                               FStar_Syntax_Syntax.Meta_pattern uu___6 in
                             (fml, uu___5) in
                           FStar_Syntax_Syntax.Tm_meta uu___4 in
                         {
                           FStar_Syntax_Syntax.n = uu___3;
                           FStar_Syntax_Syntax.pos =
                             (uu___2.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___2.FStar_Syntax_Syntax.vars)
                         } in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu___2 =
                                  let uu___3 =
                                    let uu___4 =
                                      let uu___5 =
                                        let uu___6 =
                                          FStar_Syntax_Syntax.mk_binder
                                            b.FStar_Syntax_Syntax.binder_bv in
                                        [uu___6] in
                                      let uu___6 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs uu___5 uu___6
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu___4 in
                                  [uu___3] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu___2
                                  FStar_Range.dummyRange) ibs1 fml1 in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu___2 =
                                  let uu___3 =
                                    let uu___4 =
                                      let uu___5 =
                                        let uu___6 =
                                          FStar_Syntax_Syntax.mk_binder
                                            b.FStar_Syntax_Syntax.binder_bv in
                                        [uu___6] in
                                      let uu___6 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs uu___5 uu___6
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu___4 in
                                  [uu___3] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu___2
                                  FStar_Range.dummyRange) bs2 fml2 in
                       FStar_Syntax_Util.mk_conj acc fml3)
let (unoptimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle ->
    fun tcs ->
      fun datas ->
        fun env0 ->
          let mutuals =
            FStar_List.map
              (fun ty ->
                 match ty.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid, uu___, uu___1, uu___2, uu___3, uu___4) -> lid
                 | uu___ -> failwith "Impossible!") tcs in
          let uu___ =
            let ty = FStar_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, us, uu___1, uu___2, uu___3, uu___4) -> (lid, us)
            | uu___1 -> failwith "Impossible!" in
          match uu___ with
          | (lid, us) ->
              let uu___1 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu___1 with
               | (usubst, us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs in
                   let se =
                     let uu___2 =
                       let uu___3 =
                         let uu___4 = get_haseq_axiom_lid lid in
                         (uu___4, us1, fml) in
                       FStar_Syntax_Syntax.Sig_assume uu___3 in
                     {
                       FStar_Syntax_Syntax.sigel = uu___2;
                       FStar_Syntax_Syntax.sigrng = FStar_Range.dummyRange;
                       FStar_Syntax_Syntax.sigquals = [];
                       FStar_Syntax_Syntax.sigmeta =
                         FStar_Syntax_Syntax.default_sigmeta;
                       FStar_Syntax_Syntax.sigattrs = [];
                       FStar_Syntax_Syntax.sigopts =
                         FStar_Pervasives_Native.None
                     } in
                   [se])
let (check_inductive_well_typedness :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list
            * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun lids ->
          let uu___ =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___1 ->
                    match uu___1 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu___2;
                        FStar_Syntax_Syntax.sigrng = uu___3;
                        FStar_Syntax_Syntax.sigquals = uu___4;
                        FStar_Syntax_Syntax.sigmeta = uu___5;
                        FStar_Syntax_Syntax.sigattrs = uu___6;
                        FStar_Syntax_Syntax.sigopts = uu___7;_} -> true
                    | uu___2 -> false)) in
          match uu___ with
          | (tys, datas) ->
              ((let uu___2 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3 ->
                          match uu___3 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu___4;
                              FStar_Syntax_Syntax.sigrng = uu___5;
                              FStar_Syntax_Syntax.sigquals = uu___6;
                              FStar_Syntax_Syntax.sigmeta = uu___7;
                              FStar_Syntax_Syntax.sigattrs = uu___8;
                              FStar_Syntax_Syntax.sigopts = uu___9;_} ->
                              false
                          | uu___4 -> true)) in
                if uu___2
                then
                  let uu___3 = FStar_TypeChecker_Env.get_range env in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu___3
                else ());
               (let univs =
                  if (FStar_List.length tys) = Prims.int_zero
                  then []
                  else
                    (let uu___3 =
                       let uu___4 = FStar_List.hd tys in
                       uu___4.FStar_Syntax_Syntax.sigel in
                     match uu___3 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu___4, uvs, uu___5, uu___6, uu___7, uu___8) -> uvs
                     | uu___4 -> failwith "Impossible, can't happen!") in
                let env0 = env in
                let uu___2 =
                  FStar_List.fold_right
                    (fun tc ->
                       fun uu___3 ->
                         match uu___3 with
                         | (env1, all_tcs, g) ->
                             let uu___4 = tc_tycon env1 tc in
                             (match uu___4 with
                              | (env2, tc1, tc_u, guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu___6 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu___6
                                    then
                                      let uu___7 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu___7
                                    else ());
                                   (let uu___6 =
                                      let uu___7 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu___7 in
                                    (env2, ((tc1, tc_u) :: all_tcs), uu___6)))))
                    tys (env, [], FStar_TypeChecker_Env.trivial_guard) in
                match uu___2 with
                | (env1, tcs, g) ->
                    let uu___3 =
                      FStar_List.fold_right
                        (fun se ->
                           fun uu___4 ->
                             match uu___4 with
                             | (datas1, g1) ->
                                 let uu___5 =
                                   let uu___6 = tc_data env1 tcs in uu___6 se in
                                 (match uu___5 with
                                  | (data, g') ->
                                      let uu___6 =
                                        FStar_TypeChecker_Env.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu___6))) datas
                        ([], g) in
                    (match uu___3 with
                     | (datas1, g1) ->
                         let uu___4 =
                           let tc_universe_vars =
                             FStar_List.map FStar_Pervasives_Native.snd tcs in
                           let g2 =
                             let uu___5 = g1 in
                             {
                               FStar_TypeChecker_Common.guard_f =
                                 (uu___5.FStar_TypeChecker_Common.guard_f);
                               FStar_TypeChecker_Common.deferred_to_tac =
                                 (uu___5.FStar_TypeChecker_Common.deferred_to_tac);
                               FStar_TypeChecker_Common.deferred =
                                 (uu___5.FStar_TypeChecker_Common.deferred);
                               FStar_TypeChecker_Common.univ_ineqs =
                                 (tc_universe_vars,
                                   (FStar_Pervasives_Native.snd
                                      g1.FStar_TypeChecker_Common.univ_ineqs));
                               FStar_TypeChecker_Common.implicits =
                                 (uu___5.FStar_TypeChecker_Common.implicits)
                             } in
                           (let uu___6 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "GenUniverses") in
                            if uu___6
                            then
                              let uu___7 =
                                FStar_TypeChecker_Rel.guard_to_string env1 g2 in
                              FStar_Util.print1
                                "@@@@@@Guard before (possible) generalization: %s\n"
                                uu___7
                            else ());
                           FStar_TypeChecker_Rel.force_trivial_guard env0 g2;
                           if (FStar_List.length univs) = Prims.int_zero
                           then generalize_and_inst_within env0 tcs datas1
                           else
                             (let uu___8 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  tcs in
                              (uu___8, datas1)) in
                         (match uu___4 with
                          | (tcs1, datas2) ->
                              let sig_bndle =
                                let uu___5 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                let uu___6 =
                                  FStar_List.collect
                                    (fun s -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu___5;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu___6;
                                  FStar_Syntax_Syntax.sigopts =
                                    FStar_Pervasives_Native.None
                                } in
                              (FStar_All.pipe_right tcs1
                                 (FStar_List.iter
                                    (fun se ->
                                       match se.FStar_Syntax_Syntax.sigel
                                       with
                                       | FStar_Syntax_Syntax.Sig_inductive_typ
                                           (l, univs1, binders, typ, uu___6,
                                            uu___7)
                                           ->
                                           let fail expected inferred =
                                             let uu___8 =
                                               let uu___9 =
                                                 let uu___10 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     expected in
                                                 let uu___11 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     inferred in
                                                 FStar_Util.format2
                                                   "Expected an inductive with type %s; got %s"
                                                   uu___10 uu___11 in
                                               (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                 uu___9) in
                                             FStar_Errors.raise_error uu___8
                                               se.FStar_Syntax_Syntax.sigrng in
                                           let uu___8 =
                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                               env0 l in
                                           (match uu___8 with
                                            | FStar_Pervasives_Native.None ->
                                                ()
                                            | FStar_Pervasives_Native.Some
                                                (expected_typ, uu___9) ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu___10 ->
                                                        let uu___11 =
                                                          let uu___12 =
                                                            let uu___13 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                typ in
                                                            (binders,
                                                              uu___13) in
                                                          FStar_Syntax_Syntax.Tm_arrow
                                                            uu___12 in
                                                        FStar_Syntax_Syntax.mk
                                                          uu___11
                                                          se.FStar_Syntax_Syntax.sigrng in
                                                  (univs1, body) in
                                                if
                                                  (FStar_List.length univs1)
                                                    =
                                                    (FStar_List.length
                                                       (FStar_Pervasives_Native.fst
                                                          expected_typ))
                                                then
                                                  let uu___10 =
                                                    FStar_Syntax_Subst.open_univ_vars
                                                      univs1
                                                      (FStar_Pervasives_Native.snd
                                                         inferred_typ) in
                                                  (match uu___10 with
                                                   | (uu___11, inferred) ->
                                                       let uu___12 =
                                                         FStar_Syntax_Subst.open_univ_vars
                                                           univs1
                                                           (FStar_Pervasives_Native.snd
                                                              expected_typ) in
                                                       (match uu___12 with
                                                        | (uu___13, expected)
                                                            ->
                                                            let uu___14 =
                                                              FStar_TypeChecker_Rel.teq_nosmt_force
                                                                env0 inferred
                                                                expected in
                                                            if uu___14
                                                            then ()
                                                            else
                                                              fail
                                                                expected_typ
                                                                inferred_typ))
                                                else
                                                  fail expected_typ
                                                    inferred_typ)
                                       | uu___6 -> ()));
                               (sig_bndle, tcs1, datas2))))))
let (early_prims_inductives : Prims.string Prims.list) =
  ["c_False"; "c_True"; "equals"; "h_equals"; "c_and"; "c_or"]
let (mk_discriminator_and_indexed_projectors :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.fv_qual ->
        Prims.bool ->
          FStar_TypeChecker_Env.env ->
            FStar_Ident.lident ->
              FStar_Ident.lident ->
                FStar_Syntax_Syntax.univ_names ->
                  FStar_Syntax_Syntax.binders ->
                    FStar_Syntax_Syntax.binders ->
                      FStar_Syntax_Syntax.binders ->
                        Prims.bool -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals ->
    fun attrs ->
      fun fvq ->
        fun refine_domain ->
          fun env ->
            fun tc ->
              fun lid ->
                fun uvs ->
                  fun inductive_tps ->
                    fun indices ->
                      fun fields ->
                        fun erasable ->
                          let p = FStar_Ident.range_of_lid lid in
                          let pos q = FStar_Syntax_Syntax.withinfo q p in
                          let projectee ptyp =
                            FStar_Syntax_Syntax.gen_bv "projectee"
                              (FStar_Pervasives_Native.Some p) ptyp in
                          let inst_univs =
                            FStar_List.map
                              (fun u -> FStar_Syntax_Syntax.U_name u) uvs in
                          let tps = inductive_tps in
                          let arg_typ =
                            let inst_tc =
                              let uu___ =
                                let uu___1 =
                                  let uu___2 =
                                    let uu___3 =
                                      FStar_Syntax_Syntax.lid_as_fv tc
                                        FStar_Syntax_Syntax.delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.fv_to_tm uu___3 in
                                  (uu___2, inst_univs) in
                                FStar_Syntax_Syntax.Tm_uinst uu___1 in
                              FStar_Syntax_Syntax.mk uu___ p in
                            let args =
                              FStar_All.pipe_right
                                (FStar_List.append tps indices)
                                (FStar_List.map
                                   (fun uu___ ->
                                      match uu___ with
                                      | { FStar_Syntax_Syntax.binder_bv = x;
                                          FStar_Syntax_Syntax.binder_qual =
                                            imp;
                                          FStar_Syntax_Syntax.binder_attrs =
                                            uu___1;_}
                                          ->
                                          let uu___2 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu___2, imp))) in
                            FStar_Syntax_Syntax.mk_Tm_app inst_tc args p in
                          let unrefined_arg_binder =
                            let uu___ = projectee arg_typ in
                            FStar_Syntax_Syntax.mk_binder uu___ in
                          let arg_binder =
                            if Prims.op_Negation refine_domain
                            then unrefined_arg_binder
                            else
                              (let disc_name =
                                 FStar_Syntax_Util.mk_discriminator lid in
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some p) arg_typ in
                               let sort =
                                 let disc_fvar =
                                   let uu___1 =
                                     FStar_Ident.set_lid_range disc_name p in
                                   FStar_Syntax_Syntax.fvar uu___1
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                     FStar_Pervasives_Native.None in
                                 let uu___1 =
                                   let uu___2 =
                                     let uu___3 =
                                       FStar_Syntax_Syntax.mk_Tm_uinst
                                         disc_fvar inst_univs in
                                     let uu___4 =
                                       let uu___5 =
                                         let uu___6 =
                                           FStar_Syntax_Syntax.bv_to_name x in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg uu___6 in
                                       [uu___5] in
                                     FStar_Syntax_Syntax.mk_Tm_app uu___3
                                       uu___4 p in
                                   FStar_Syntax_Util.b2t uu___2 in
                                 FStar_Syntax_Util.refine x uu___1 in
                               let uu___1 =
                                 let uu___2 = projectee arg_typ in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___2.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___2.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = sort
                                 } in
                               FStar_Syntax_Syntax.mk_binder uu___1) in
                          let ntps = FStar_List.length tps in
                          let all_params =
                            let uu___ =
                              FStar_List.map
                                (fun b ->
                                   let uu___1 = b in
                                   {
                                     FStar_Syntax_Syntax.binder_bv =
                                       (uu___1.FStar_Syntax_Syntax.binder_bv);
                                     FStar_Syntax_Syntax.binder_qual =
                                       (FStar_Pervasives_Native.Some
                                          FStar_Syntax_Syntax.imp_tag);
                                     FStar_Syntax_Syntax.binder_attrs =
                                       (uu___1.FStar_Syntax_Syntax.binder_attrs)
                                   }) tps in
                            FStar_List.append uu___ fields in
                          let imp_binders =
                            FStar_All.pipe_right
                              (FStar_List.append tps indices)
                              (FStar_List.map
                                 (fun b ->
                                    let uu___ = b in
                                    {
                                      FStar_Syntax_Syntax.binder_bv =
                                        (uu___.FStar_Syntax_Syntax.binder_bv);
                                      FStar_Syntax_Syntax.binder_qual =
                                        (FStar_Pervasives_Native.Some
                                           FStar_Syntax_Syntax.imp_tag);
                                      FStar_Syntax_Syntax.binder_attrs =
                                        (uu___.FStar_Syntax_Syntax.binder_attrs)
                                    })) in
                          let early_prims_inductive =
                            (let uu___ =
                               FStar_TypeChecker_Env.current_module env in
                             FStar_Ident.lid_equals
                               FStar_Parser_Const.prims_lid uu___)
                              &&
                              (FStar_List.existsb
                                 (fun s ->
                                    let uu___ =
                                      let uu___1 =
                                        FStar_Ident.ident_of_lid tc in
                                      FStar_Ident.string_of_id uu___1 in
                                    s = uu___) early_prims_inductives) in
                          let discriminator_ses =
                            if fvq <> FStar_Syntax_Syntax.Data_ctor
                            then []
                            else
                              (let discriminator_name =
                                 FStar_Syntax_Util.mk_discriminator lid in
                               let no_decl = false in
                               let only_decl =
                                 early_prims_inductive ||
                                   (let uu___1 =
                                      let uu___2 =
                                        FStar_TypeChecker_Env.current_module
                                          env in
                                      FStar_Ident.string_of_lid uu___2 in
                                    FStar_Options.dont_gen_projectors uu___1) in
                               let quals =
                                 let uu___1 =
                                   FStar_List.filter
                                     (fun uu___2 ->
                                        match uu___2 with
                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                            -> true
                                        | FStar_Syntax_Syntax.NoExtract ->
                                            true
                                        | FStar_Syntax_Syntax.Private -> true
                                        | uu___3 -> false) iquals in
                                 FStar_List.append
                                   ((FStar_Syntax_Syntax.Discriminator lid)
                                   ::
                                   (if only_decl
                                    then
                                      [FStar_Syntax_Syntax.Logic;
                                      FStar_Syntax_Syntax.Assumption]
                                    else [])) uu___1 in
                               let binders =
                                 FStar_List.append imp_binders
                                   [unrefined_arg_binder] in
                               let t =
                                 let bool_typ =
                                   if erasable
                                   then
                                     FStar_Syntax_Syntax.mk_GTotal
                                       FStar_Syntax_Util.t_bool
                                   else
                                     FStar_Syntax_Syntax.mk_Total
                                       FStar_Syntax_Util.t_bool in
                                 let uu___1 =
                                   FStar_Syntax_Util.arrow binders bool_typ in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.close_univ_vars uvs)
                                   uu___1 in
                               let decl =
                                 let uu___1 =
                                   FStar_Ident.range_of_lid
                                     discriminator_name in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_declare_typ
                                        (discriminator_name, uvs, t));
                                   FStar_Syntax_Syntax.sigrng = uu___1;
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = attrs;
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 } in
                               (let uu___2 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "LogTypes") in
                                if uu___2
                                then
                                  let uu___3 =
                                    FStar_Syntax_Print.sigelt_to_string decl in
                                  FStar_Util.print1
                                    "Declaration of a discriminator %s\n"
                                    uu___3
                                else ());
                               if only_decl
                               then [decl]
                               else
                                 (let body =
                                    if Prims.op_Negation refine_domain
                                    then FStar_Syntax_Util.exp_true_bool
                                    else
                                      (let arg_pats =
                                         FStar_All.pipe_right all_params
                                           (FStar_List.mapi
                                              (fun j ->
                                                 fun uu___4 ->
                                                   match uu___4 with
                                                   | {
                                                       FStar_Syntax_Syntax.binder_bv
                                                         = x;
                                                       FStar_Syntax_Syntax.binder_qual
                                                         = imp;
                                                       FStar_Syntax_Syntax.binder_attrs
                                                         = uu___5;_}
                                                       ->
                                                       let b =
                                                         FStar_Syntax_Syntax.is_implicit
                                                           imp in
                                                       if b && (j < ntps)
                                                       then
                                                         let uu___6 =
                                                           let uu___7 =
                                                             let uu___8 =
                                                               let uu___9 =
                                                                 let uu___10
                                                                   =
                                                                   FStar_Ident.string_of_id
                                                                    x.FStar_Syntax_Syntax.ppname in
                                                                 FStar_Syntax_Syntax.gen_bv
                                                                   uu___10
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Syntax_Syntax.tun in
                                                               (uu___9,
                                                                 FStar_Syntax_Syntax.tun) in
                                                             FStar_Syntax_Syntax.Pat_dot_term
                                                               uu___8 in
                                                           pos uu___7 in
                                                         (uu___6, b)
                                                       else
                                                         (let uu___7 =
                                                            let uu___8 =
                                                              let uu___9 =
                                                                let uu___10 =
                                                                  FStar_Ident.string_of_id
                                                                    x.FStar_Syntax_Syntax.ppname in
                                                                FStar_Syntax_Syntax.gen_bv
                                                                  uu___10
                                                                  FStar_Pervasives_Native.None
                                                                  FStar_Syntax_Syntax.tun in
                                                              FStar_Syntax_Syntax.Pat_wild
                                                                uu___9 in
                                                            pos uu___8 in
                                                          (uu___7, b)))) in
                                       let pat_true =
                                         let uu___4 =
                                           let uu___5 =
                                             let uu___6 =
                                               let uu___7 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   lid
                                                   FStar_Syntax_Syntax.delta_constant
                                                   (FStar_Pervasives_Native.Some
                                                      fvq) in
                                               (uu___7, arg_pats) in
                                             FStar_Syntax_Syntax.Pat_cons
                                               uu___6 in
                                           pos uu___5 in
                                         (uu___4,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_true_bool) in
                                       let pat_false =
                                         let uu___4 =
                                           let uu___5 =
                                             let uu___6 =
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 FStar_Syntax_Syntax.tun in
                                             FStar_Syntax_Syntax.Pat_wild
                                               uu___6 in
                                           pos uu___5 in
                                         (uu___4,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_false_bool) in
                                       let arg_exp =
                                         FStar_Syntax_Syntax.bv_to_name
                                           unrefined_arg_binder.FStar_Syntax_Syntax.binder_bv in
                                       let uu___4 =
                                         let uu___5 =
                                           let uu___6 =
                                             let uu___7 =
                                               FStar_Syntax_Util.branch
                                                 pat_true in
                                             let uu___8 =
                                               let uu___9 =
                                                 FStar_Syntax_Util.branch
                                                   pat_false in
                                               [uu___9] in
                                             uu___7 :: uu___8 in
                                           (arg_exp,
                                             FStar_Pervasives_Native.None,
                                             uu___6) in
                                         FStar_Syntax_Syntax.Tm_match uu___5 in
                                       FStar_Syntax_Syntax.mk uu___4 p) in
                                  let dd =
                                    FStar_Syntax_Syntax.Delta_equational_at_level
                                      Prims.int_one in
                                  let imp =
                                    FStar_Syntax_Util.abs binders body
                                      FStar_Pervasives_Native.None in
                                  let lbtyp =
                                    if no_decl
                                    then t
                                    else FStar_Syntax_Syntax.tun in
                                  let lb =
                                    let uu___3 =
                                      let uu___4 =
                                        FStar_Syntax_Syntax.lid_as_fv
                                          discriminator_name dd
                                          FStar_Pervasives_Native.None in
                                      FStar_Pervasives.Inr uu___4 in
                                    let uu___4 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        imp in
                                    FStar_Syntax_Util.mk_letbinding uu___3
                                      uvs lbtyp
                                      FStar_Parser_Const.effect_Tot_lid
                                      uu___4 [] FStar_Range.dummyRange in
                                  let impl =
                                    let uu___3 =
                                      let uu___4 =
                                        let uu___5 =
                                          let uu___6 =
                                            let uu___7 =
                                              FStar_All.pipe_right
                                                lb.FStar_Syntax_Syntax.lbname
                                                FStar_Util.right in
                                            FStar_All.pipe_right uu___7
                                              (fun fv ->
                                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                          [uu___6] in
                                        ((false, [lb]), uu___5) in
                                      FStar_Syntax_Syntax.Sig_let uu___4 in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu___3;
                                      FStar_Syntax_Syntax.sigrng = p;
                                      FStar_Syntax_Syntax.sigquals = quals;
                                      FStar_Syntax_Syntax.sigmeta =
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs = attrs;
                                      FStar_Syntax_Syntax.sigopts =
                                        FStar_Pervasives_Native.None
                                    } in
                                  (let uu___4 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "LogTypes") in
                                   if uu___4
                                   then
                                     let uu___5 =
                                       FStar_Syntax_Print.sigelt_to_string
                                         impl in
                                     FStar_Util.print1
                                       "Implementation of a discriminator %s\n"
                                       uu___5
                                   else ());
                                  [decl; impl])) in
                          let arg_exp =
                            FStar_Syntax_Syntax.bv_to_name
                              arg_binder.FStar_Syntax_Syntax.binder_bv in
                          let binders =
                            FStar_List.append imp_binders [arg_binder] in
                          let arg =
                            FStar_Syntax_Util.arg_of_non_null_binder
                              arg_binder in
                          let subst =
                            FStar_All.pipe_right fields
                              (FStar_List.mapi
                                 (fun i ->
                                    fun uu___ ->
                                      match uu___ with
                                      | { FStar_Syntax_Syntax.binder_bv = a;
                                          FStar_Syntax_Syntax.binder_qual =
                                            uu___1;
                                          FStar_Syntax_Syntax.binder_attrs =
                                            uu___2;_}
                                          ->
                                          let field_name =
                                            FStar_Syntax_Util.mk_field_projector_name
                                              lid a i in
                                          let field_proj_tm =
                                            let uu___3 =
                                              let uu___4 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  field_name
                                                  (FStar_Syntax_Syntax.Delta_equational_at_level
                                                     Prims.int_one)
                                                  FStar_Pervasives_Native.None in
                                              FStar_Syntax_Syntax.fv_to_tm
                                                uu___4 in
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              uu___3 inst_univs in
                                          let proj =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              field_proj_tm [arg] p in
                                          FStar_Syntax_Syntax.NT (a, proj))) in
                          let projectors_ses =
                            let uu___ =
                              FStar_All.pipe_right fields
                                (FStar_List.mapi
                                   (fun i ->
                                      fun uu___1 ->
                                        match uu___1 with
                                        | {
                                            FStar_Syntax_Syntax.binder_bv = x;
                                            FStar_Syntax_Syntax.binder_qual =
                                              uu___2;
                                            FStar_Syntax_Syntax.binder_attrs
                                              = uu___3;_}
                                            ->
                                            let p1 =
                                              FStar_Syntax_Syntax.range_of_bv
                                                x in
                                            let field_name =
                                              FStar_Syntax_Util.mk_field_projector_name
                                                lid x i in
                                            let t =
                                              let result_comp =
                                                let t1 =
                                                  FStar_Syntax_Subst.subst
                                                    subst
                                                    x.FStar_Syntax_Syntax.sort in
                                                if erasable
                                                then
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t1
                                                else
                                                  FStar_Syntax_Syntax.mk_Total
                                                    t1 in
                                              let uu___4 =
                                                FStar_Syntax_Util.arrow
                                                  binders result_comp in
                                              FStar_All.pipe_left
                                                (FStar_Syntax_Subst.close_univ_vars
                                                   uvs) uu___4 in
                                            let only_decl =
                                              early_prims_inductive ||
                                                (let uu___4 =
                                                   let uu___5 =
                                                     FStar_TypeChecker_Env.current_module
                                                       env in
                                                   FStar_Ident.string_of_lid
                                                     uu___5 in
                                                 FStar_Options.dont_gen_projectors
                                                   uu___4) in
                                            let no_decl = false in
                                            let quals q =
                                              if only_decl
                                              then
                                                FStar_Syntax_Syntax.Assumption
                                                :: q
                                              else q in
                                            let quals1 =
                                              let iquals1 =
                                                FStar_All.pipe_right iquals
                                                  (FStar_List.filter
                                                     (fun uu___4 ->
                                                        match uu___4 with
                                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                                            -> true
                                                        | FStar_Syntax_Syntax.NoExtract
                                                            -> true
                                                        | FStar_Syntax_Syntax.Private
                                                            -> true
                                                        | uu___5 -> false)) in
                                              quals
                                                ((FStar_Syntax_Syntax.Projector
                                                    (lid,
                                                      (x.FStar_Syntax_Syntax.ppname)))
                                                :: iquals1) in
                                            let attrs1 =
                                              FStar_List.append
                                                (if only_decl
                                                 then []
                                                 else
                                                   [FStar_Syntax_Util.attr_substitute])
                                                attrs in
                                            let decl =
                                              let uu___4 =
                                                FStar_Ident.range_of_lid
                                                  field_name in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                                     (field_name, uvs, t));
                                                FStar_Syntax_Syntax.sigrng =
                                                  uu___4;
                                                FStar_Syntax_Syntax.sigquals
                                                  = quals1;
                                                FStar_Syntax_Syntax.sigmeta =
                                                  FStar_Syntax_Syntax.default_sigmeta;
                                                FStar_Syntax_Syntax.sigattrs
                                                  = attrs1;
                                                FStar_Syntax_Syntax.sigopts =
                                                  FStar_Pervasives_Native.None
                                              } in
                                            ((let uu___5 =
                                                FStar_TypeChecker_Env.debug
                                                  env
                                                  (FStar_Options.Other
                                                     "LogTypes") in
                                              if uu___5
                                              then
                                                let uu___6 =
                                                  FStar_Syntax_Print.sigelt_to_string
                                                    decl in
                                                FStar_Util.print1
                                                  "Declaration of a projector %s\n"
                                                  uu___6
                                              else ());
                                             if only_decl
                                             then [decl]
                                             else
                                               (let projection =
                                                  let uu___6 =
                                                    FStar_Ident.string_of_id
                                                      x.FStar_Syntax_Syntax.ppname in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    uu___6
                                                    FStar_Pervasives_Native.None
                                                    FStar_Syntax_Syntax.tun in
                                                let arg_pats =
                                                  FStar_All.pipe_right
                                                    all_params
                                                    (FStar_List.mapi
                                                       (fun j ->
                                                          fun uu___6 ->
                                                            match uu___6 with
                                                            | {
                                                                FStar_Syntax_Syntax.binder_bv
                                                                  = x1;
                                                                FStar_Syntax_Syntax.binder_qual
                                                                  = imp;
                                                                FStar_Syntax_Syntax.binder_attrs
                                                                  = uu___7;_}
                                                                ->
                                                                let b =
                                                                  FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                if
                                                                  (i + ntps)
                                                                    = j
                                                                then
                                                                  let uu___8
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                  (uu___8, b)
                                                                else
                                                                  if
                                                                    b &&
                                                                    (j < ntps)
                                                                  then
                                                                    (
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    x1.FStar_Syntax_Syntax.ppname in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    uu___13
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu___12,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu___11 in
                                                                    pos
                                                                    uu___10 in
                                                                    (uu___9,
                                                                    b))
                                                                  else
                                                                    (
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    x1.FStar_Syntax_Syntax.ppname in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    uu___13
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu___12 in
                                                                    pos
                                                                    uu___11 in
                                                                    (uu___10,
                                                                    b)))) in
                                                let pat =
                                                  let uu___6 =
                                                    let uu___7 =
                                                      let uu___8 =
                                                        let uu___9 =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            lid
                                                            FStar_Syntax_Syntax.delta_constant
                                                            (FStar_Pervasives_Native.Some
                                                               fvq) in
                                                        (uu___9, arg_pats) in
                                                      FStar_Syntax_Syntax.Pat_cons
                                                        uu___8 in
                                                    pos uu___7 in
                                                  let uu___7 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      projection in
                                                  (uu___6,
                                                    FStar_Pervasives_Native.None,
                                                    uu___7) in
                                                let body =
                                                  let uu___6 =
                                                    let uu___7 =
                                                      let uu___8 =
                                                        let uu___9 =
                                                          FStar_Syntax_Util.branch
                                                            pat in
                                                        [uu___9] in
                                                      (arg_exp,
                                                        FStar_Pervasives_Native.None,
                                                        uu___8) in
                                                    FStar_Syntax_Syntax.Tm_match
                                                      uu___7 in
                                                  FStar_Syntax_Syntax.mk
                                                    uu___6 p1 in
                                                let imp =
                                                  FStar_Syntax_Util.abs
                                                    binders body
                                                    FStar_Pervasives_Native.None in
                                                let dd =
                                                  FStar_Syntax_Syntax.Delta_equational_at_level
                                                    Prims.int_one in
                                                let lbtyp =
                                                  if no_decl
                                                  then t
                                                  else
                                                    FStar_Syntax_Syntax.tun in
                                                let lb =
                                                  let uu___6 =
                                                    let uu___7 =
                                                      FStar_Syntax_Syntax.lid_as_fv
                                                        field_name dd
                                                        FStar_Pervasives_Native.None in
                                                    FStar_Pervasives.Inr
                                                      uu___7 in
                                                  let uu___7 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs imp in
                                                  {
                                                    FStar_Syntax_Syntax.lbname
                                                      = uu___6;
                                                    FStar_Syntax_Syntax.lbunivs
                                                      = uvs;
                                                    FStar_Syntax_Syntax.lbtyp
                                                      = lbtyp;
                                                    FStar_Syntax_Syntax.lbeff
                                                      =
                                                      FStar_Parser_Const.effect_Tot_lid;
                                                    FStar_Syntax_Syntax.lbdef
                                                      = uu___7;
                                                    FStar_Syntax_Syntax.lbattrs
                                                      = [];
                                                    FStar_Syntax_Syntax.lbpos
                                                      =
                                                      FStar_Range.dummyRange
                                                  } in
                                                let impl =
                                                  let uu___6 =
                                                    let uu___7 =
                                                      let uu___8 =
                                                        let uu___9 =
                                                          let uu___10 =
                                                            FStar_All.pipe_right
                                                              lb.FStar_Syntax_Syntax.lbname
                                                              FStar_Util.right in
                                                          FStar_All.pipe_right
                                                            uu___10
                                                            (fun fv ->
                                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                        [uu___9] in
                                                      ((false, [lb]), uu___8) in
                                                    FStar_Syntax_Syntax.Sig_let
                                                      uu___7 in
                                                  {
                                                    FStar_Syntax_Syntax.sigel
                                                      = uu___6;
                                                    FStar_Syntax_Syntax.sigrng
                                                      = p1;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = quals1;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      =
                                                      FStar_Syntax_Syntax.default_sigmeta;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = attrs1;
                                                    FStar_Syntax_Syntax.sigopts
                                                      =
                                                      FStar_Pervasives_Native.None
                                                  } in
                                                (let uu___7 =
                                                   FStar_TypeChecker_Env.debug
                                                     env
                                                     (FStar_Options.Other
                                                        "LogTypes") in
                                                 if uu___7
                                                 then
                                                   let uu___8 =
                                                     FStar_Syntax_Print.sigelt_to_string
                                                       impl in
                                                   FStar_Util.print1
                                                     "Implementation of a projector %s\n"
                                                     uu___8
                                                 else ());
                                                if no_decl
                                                then [impl]
                                                else [decl; impl])))) in
                            FStar_All.pipe_right uu___ FStar_List.flatten in
                          FStar_List.append discriminator_ses projectors_ses
let (mk_data_operations :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals ->
    fun attrs ->
      fun env ->
        fun tcs ->
          fun se ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_datacon
                (constr_lid, uvs, t, typ_lid, n_typars, uu___) ->
                let uu___1 = FStar_Syntax_Subst.univ_var_opening uvs in
                (match uu___1 with
                 | (univ_opening, uvs1) ->
                     let t1 = FStar_Syntax_Subst.subst univ_opening t in
                     let uu___2 = FStar_Syntax_Util.arrow_formals t1 in
                     (match uu___2 with
                      | (formals, uu___3) ->
                          let uu___4 =
                            let tps_opt =
                              FStar_Util.find_map tcs
                                (fun se1 ->
                                   let uu___5 =
                                     let uu___6 =
                                       let uu___7 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Util.must uu___7 in
                                     FStar_Ident.lid_equals typ_lid uu___6 in
                                   if uu___5
                                   then
                                     match se1.FStar_Syntax_Syntax.sigel with
                                     | FStar_Syntax_Syntax.Sig_inductive_typ
                                         (uu___6, uvs', tps, typ0, uu___7,
                                          constrs)
                                         ->
                                         FStar_Pervasives_Native.Some
                                           (tps, typ0,
                                             ((FStar_List.length constrs) >
                                                Prims.int_one))
                                     | uu___6 -> failwith "Impossible"
                                   else FStar_Pervasives_Native.None) in
                            match tps_opt with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None ->
                                let uu___5 =
                                  FStar_Ident.lid_equals typ_lid
                                    FStar_Parser_Const.exn_lid in
                                if uu___5
                                then ([], FStar_Syntax_Util.ktype0, true)
                                else
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                      "Unexpected data constructor")
                                    se.FStar_Syntax_Syntax.sigrng in
                          (match uu___4 with
                           | (inductive_tps, typ0, should_refine) ->
                               let inductive_tps1 =
                                 FStar_Syntax_Subst.subst_binders
                                   univ_opening inductive_tps in
                               let typ01 =
                                 FStar_Syntax_Subst.subst univ_opening typ0 in
                               let uu___5 =
                                 FStar_Syntax_Util.arrow_formals typ01 in
                               (match uu___5 with
                                | (indices, uu___6) ->
                                    let refine_domain =
                                      let uu___7 =
                                        FStar_All.pipe_right
                                          se.FStar_Syntax_Syntax.sigquals
                                          (FStar_Util.for_some
                                             (fun uu___8 ->
                                                match uu___8 with
                                                | FStar_Syntax_Syntax.RecordConstructor
                                                    uu___9 -> true
                                                | uu___9 -> false)) in
                                      if uu___7 then false else should_refine in
                                    let fv_qual =
                                      let filter_records uu___7 =
                                        match uu___7 with
                                        | FStar_Syntax_Syntax.RecordConstructor
                                            (uu___8, fns) ->
                                            FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Syntax.Record_ctor
                                                 (typ_lid, fns))
                                        | uu___8 ->
                                            FStar_Pervasives_Native.None in
                                      let uu___7 =
                                        FStar_Util.find_map
                                          se.FStar_Syntax_Syntax.sigquals
                                          filter_records in
                                      match uu___7 with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Syntax_Syntax.Data_ctor
                                      | FStar_Pervasives_Native.Some q -> q in
                                    let fields =
                                      let uu___7 =
                                        FStar_Util.first_N n_typars formals in
                                      match uu___7 with
                                      | (imp_tps, fields1) ->
                                          let rename =
                                            FStar_List.map2
                                              (fun uu___8 ->
                                                 fun uu___9 ->
                                                   match (uu___8, uu___9)
                                                   with
                                                   | ({
                                                        FStar_Syntax_Syntax.binder_bv
                                                          = x;
                                                        FStar_Syntax_Syntax.binder_qual
                                                          = uu___10;
                                                        FStar_Syntax_Syntax.binder_attrs
                                                          = uu___11;_},
                                                      {
                                                        FStar_Syntax_Syntax.binder_bv
                                                          = x';
                                                        FStar_Syntax_Syntax.binder_qual
                                                          = uu___12;
                                                        FStar_Syntax_Syntax.binder_attrs
                                                          = uu___13;_})
                                                       ->
                                                       let uu___14 =
                                                         let uu___15 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x' in
                                                         (x, uu___15) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu___14) imp_tps
                                              inductive_tps1 in
                                          FStar_Syntax_Subst.subst_binders
                                            rename fields1 in
                                    let erasable =
                                      FStar_Syntax_Util.has_attribute
                                        se.FStar_Syntax_Syntax.sigattrs
                                        FStar_Parser_Const.erasable_attr in
                                    mk_discriminator_and_indexed_projectors
                                      iquals attrs fv_qual refine_domain env
                                      typ_lid constr_lid uvs1 inductive_tps1
                                      indices fields erasable))))
            | uu___ -> []