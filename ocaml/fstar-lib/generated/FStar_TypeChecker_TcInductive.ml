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
          (tc, uvs, tps, n_uniform, k, mutuals, data) ->
          let env0 = env in
          let uu___ = FStar_Syntax_Subst.univ_var_opening uvs in
          (match uu___ with
           | (usubst, uvs1) ->
               let uu___1 =
                 let uu___2 = FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                 let uu___3 = FStar_Syntax_Subst.subst_binders usubst tps in
                 let uu___4 =
                   let uu___5 =
                     FStar_Syntax_Subst.shift_subst
                       (FStar_Compiler_List.length tps) usubst in
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
                                          (((FStar_Syntax_Util.is_eqtype_no_unrefine
                                               t)
                                              &&
                                              (let uu___6 =
                                                 FStar_Compiler_Effect.op_Bar_Greater
                                                   s.FStar_Syntax_Syntax.sigquals
                                                   (FStar_Compiler_List.contains
                                                      FStar_Syntax_Syntax.Noeq) in
                                               Prims.op_Negation uu___6))
                                             &&
                                             (let uu___6 =
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_Compiler_List.contains
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
                                                FStar_Compiler_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains noeq/unopteq qualifiers"
                                                  uu___9 uu___10 in
                                              (FStar_Errors_Codes.Error_InductiveAnnotNotAType,
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
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1) in
                                              let uu___9 =
                                                let uu___10 =
                                                  let uu___11 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_Compiler_List.length
                                                         tps3) usubst1 in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu___11 in
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  indices uu___10 in
                                              FStar_Compiler_List.op_At
                                                uu___8 uu___9 in
                                            let uu___8 =
                                              let uu___9 =
                                                let uu___10 =
                                                  let uu___11 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_Compiler_List.length
                                                          tps3)
                                                         +
                                                         (FStar_Compiler_List.length
                                                            indices)) usubst1 in
                                                  FStar_Syntax_Subst.subst
                                                    uu___11 in
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  t uu___10 in
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
                                                  (FStar_Compiler_List.length
                                                     tps4) usubst1 in
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
                                                     {
                                                       FStar_Syntax_Syntax.sigel
                                                         =
                                                         (FStar_Syntax_Syntax.Sig_inductive_typ
                                                            (tc, uvs2, tps5,
                                                              n_uniform, k5,
                                                              mutuals, data));
                                                       FStar_Syntax_Syntax.sigrng
                                                         =
                                                         (s.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (s.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (s.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (s.FStar_Syntax_Syntax.sigattrs);
                                                       FStar_Syntax_Syntax.sigopts
                                                         =
                                                         (s.FStar_Syntax_Syntax.sigopts)
                                                     }, u, guard1))))))))))
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
                          FStar_Compiler_Util.find_map tcs
                            (fun uu___3 ->
                               match uu___3 with
                               | (se1, u_tc) ->
                                   let uu___4 =
                                     let uu___5 =
                                       let uu___6 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Compiler_Util.must uu___6 in
                                     FStar_Ident.lid_equals tc_lid uu___5 in
                                   if uu___4
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu___5, uu___6, tps, uu___7,
                                           uu___8, uu___9, uu___10)
                                          ->
                                          let tps1 =
                                            let uu___11 =
                                              FStar_Compiler_Effect.op_Bar_Greater
                                                tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst) in
                                            FStar_Compiler_Effect.op_Bar_Greater
                                              uu___11
                                              (FStar_Compiler_List.map
                                                 (fun x ->
                                                    {
                                                      FStar_Syntax_Syntax.binder_bv
                                                        =
                                                        (x.FStar_Syntax_Syntax.binder_bv);
                                                      FStar_Syntax_Syntax.binder_qual
                                                        =
                                                        (FStar_Pervasives_Native.Some
                                                           FStar_Syntax_Syntax.imp_tag);
                                                      FStar_Syntax_Syntax.binder_positivity
                                                        =
                                                        (x.FStar_Syntax_Syntax.binder_positivity);
                                                      FStar_Syntax_Syntax.binder_attrs
                                                        =
                                                        (x.FStar_Syntax_Syntax.binder_attrs)
                                                    })) in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1 in
                                          let uu___11 =
                                            let uu___12 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2 in
                                            (uu___12, tps2, u_tc) in
                                          FStar_Pervasives_Native.Some
                                            uu___11
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
                                (FStar_Errors_Codes.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng in
                      (match uu___2 with
                       | (env2, tps, u_tc) ->
                           let uu___3 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_Compiler_List.op_At
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1 in
                             let uu___4 =
                               let uu___5 = FStar_Syntax_Subst.compress t2 in
                               uu___5.FStar_Syntax_Syntax.n in
                             match uu___4 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs, res) ->
                                 let uu___5 =
                                   FStar_Compiler_Util.first_N ntps bs in
                                 (match uu___5 with
                                  | (uu___6, bs') ->
                                      let t3 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (bs', res))
                                          t2.FStar_Syntax_Syntax.pos in
                                      let subst =
                                        FStar_Compiler_Effect.op_Bar_Greater
                                          tps
                                          (FStar_Compiler_List.mapi
                                             (fun i ->
                                                fun uu___7 ->
                                                  match uu___7 with
                                                  | {
                                                      FStar_Syntax_Syntax.binder_bv
                                                        = x;
                                                      FStar_Syntax_Syntax.binder_qual
                                                        = uu___8;
                                                      FStar_Syntax_Syntax.binder_positivity
                                                        = uu___9;
                                                      FStar_Syntax_Syntax.binder_attrs
                                                        = uu___10;_}
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
                                                (FStar_Errors_Codes.Fatal_UnexpectedConstructorType,
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
                                    FStar_Compiler_Util.print3
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
                                                let g_uvs =
                                                  let uu___8 =
                                                    let uu___9 =
                                                      FStar_Syntax_Subst.compress
                                                        head in
                                                    uu___9.FStar_Syntax_Syntax.n in
                                                  match uu___8 with
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                      ({
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           FStar_Syntax_Syntax.Tm_fvar
                                                           fv;
                                                         FStar_Syntax_Syntax.pos
                                                           = uu___9;
                                                         FStar_Syntax_Syntax.vars
                                                           = uu___10;
                                                         FStar_Syntax_Syntax.hash_code
                                                           = uu___11;_},
                                                       tuvs)
                                                      when
                                                      FStar_Syntax_Syntax.fv_eq_lid
                                                        fv tc_lid
                                                      ->
                                                      if
                                                        (FStar_Compiler_List.length
                                                           _uvs1)
                                                          =
                                                          (FStar_Compiler_List.length
                                                             tuvs)
                                                      then
                                                        FStar_Compiler_List.fold_left2
                                                          (fun g ->
                                                             fun u1 ->
                                                               fun u2 ->
                                                                 let uu___12
                                                                   =
                                                                   let uu___13
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Compiler_Range_Type.dummyRange in
                                                                   let uu___14
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Compiler_Range_Type.dummyRange in
                                                                   FStar_TypeChecker_Rel.teq
                                                                    env'1
                                                                    uu___13
                                                                    uu___14 in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g uu___12)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          tuvs _uvs1
                                                      else
                                                        FStar_Errors.raise_error
                                                          (FStar_Errors_Codes.Fatal_UnexpectedConstructorType,
                                                            "Length of annotated universes does not match inferred universes")
                                                          se.FStar_Syntax_Syntax.sigrng
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv when
                                                      FStar_Syntax_Syntax.fv_eq_lid
                                                        fv tc_lid
                                                      ->
                                                      FStar_TypeChecker_Env.trivial_guard
                                                  | uu___9 ->
                                                      let uu___10 =
                                                        let uu___11 =
                                                          let uu___12 =
                                                            FStar_Syntax_Print.lid_to_string
                                                              tc_lid in
                                                          let uu___13 =
                                                            FStar_Syntax_Print.term_to_string
                                                              head in
                                                          FStar_Compiler_Util.format2
                                                            "Expected a constructor of type %s; got %s"
                                                            uu___12 uu___13 in
                                                        (FStar_Errors_Codes.Fatal_UnexpectedConstructorType,
                                                          uu___11) in
                                                      FStar_Errors.raise_error
                                                        uu___10
                                                        se.FStar_Syntax_Syntax.sigrng in
                                                let g =
                                                  FStar_Compiler_List.fold_left2
                                                    (fun g1 ->
                                                       fun uu___8 ->
                                                         fun u_x ->
                                                           match uu___8 with
                                                           | {
                                                               FStar_Syntax_Syntax.binder_bv
                                                                 = x;
                                                               FStar_Syntax_Syntax.binder_qual
                                                                 = uu___9;
                                                               FStar_Syntax_Syntax.binder_positivity
                                                                 = uu___10;
                                                               FStar_Syntax_Syntax.binder_attrs
                                                                 = uu___11;_}
                                                               ->
                                                               let uu___12 =
                                                                 FStar_TypeChecker_Rel.universe_inequality
                                                                   u_x u_tc in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g1 uu___12)
                                                    g_uvs arguments1 us in
                                                (FStar_Errors.stop_if_err ();
                                                 (let p_args =
                                                    let uu___9 =
                                                      FStar_Compiler_Util.first_N
                                                        (FStar_Compiler_List.length
                                                           tps) args in
                                                    FStar_Pervasives_Native.fst
                                                      uu___9 in
                                                  FStar_Compiler_List.iter2
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
                                                              FStar_Syntax_Syntax.binder_positivity
                                                                = uu___13;
                                                              FStar_Syntax_Syntax.binder_attrs
                                                                = uu___14;_},
                                                            (t2, uu___15)) ->
                                                             let uu___16 =
                                                               let uu___17 =
                                                                 FStar_Syntax_Subst.compress
                                                                   t2 in
                                                               uu___17.FStar_Syntax_Syntax.n in
                                                             (match uu___16
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_name
                                                                  bv' when
                                                                  FStar_Syntax_Syntax.bv_eq
                                                                    bv bv'
                                                                  -> ()
                                                              | uu___17 ->
                                                                  let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv in
                                                                    let uu___21
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    FStar_Compiler_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu___20
                                                                    uu___21 in
                                                                    (FStar_Errors_Codes.Error_BadInductiveParam,
                                                                    uu___19) in
                                                                  FStar_Errors.raise_error
                                                                    uu___18
                                                                    t2.FStar_Syntax_Syntax.pos))
                                                    tps p_args;
                                                  (let ty =
                                                     let uu___10 =
                                                       unfold_whnf env2
                                                         res_lcomp.FStar_TypeChecker_Common.res_typ in
                                                     FStar_Compiler_Effect.op_Bar_Greater
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
                                                            FStar_Compiler_Util.format2
                                                              "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                              uu___15 uu___16 in
                                                          (FStar_Errors_Codes.Fatal_WrongResultTypeAfterConstrutor,
                                                            uu___14) in
                                                        FStar_Errors.raise_error
                                                          uu___13
                                                          se.FStar_Syntax_Syntax.sigrng);
                                                   (let t2 =
                                                      let uu___11 =
                                                        let uu___12 =
                                                          FStar_Compiler_Effect.op_Bar_Greater
                                                            tps
                                                            (FStar_Compiler_List.map
                                                               (fun b ->
                                                                  {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    =
                                                                    (b.FStar_Syntax_Syntax.binder_bv);
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true));
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    =
                                                                    (b.FStar_Syntax_Syntax.binder_positivity);
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    =
                                                                    (b.FStar_Syntax_Syntax.binder_attrs)
                                                                  })) in
                                                        FStar_Compiler_List.op_At
                                                          uu___12 arguments1 in
                                                      let uu___12 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          result1 in
                                                      FStar_Syntax_Util.arrow
                                                        uu___11 uu___12 in
                                                    let t3 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        _uvs1 t2 in
                                                    ({
                                                       FStar_Syntax_Syntax.sigel
                                                         =
                                                         (FStar_Syntax_Syntax.Sig_datacon
                                                            (c, _uvs1, t3,
                                                              tc_lid, ntps,
                                                              mutual_tcs));
                                                       FStar_Syntax_Syntax.sigrng
                                                         =
                                                         (se.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (se.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (se.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (se.FStar_Syntax_Syntax.sigattrs);
                                                       FStar_Syntax_Syntax.sigopts
                                                         =
                                                         (se.FStar_Syntax_Syntax.sigopts)
                                                     }, g)))))))))))))
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
          FStar_Compiler_Effect.op_Bar_Greater tcs
            (FStar_Compiler_List.map
               (fun uu___ ->
                  match uu___ with
                  | (se, uu___1) ->
                      (match se.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (uu___2, uu___3, tps, uu___4, k, uu___5, uu___6)
                           ->
                           let uu___7 =
                             let uu___8 = FStar_Syntax_Syntax.mk_Total k in
                             FStar_Compiler_Effect.op_Less_Bar
                               (FStar_Syntax_Util.arrow tps) uu___8 in
                           FStar_Syntax_Syntax.null_binder uu___7
                       | uu___2 -> failwith "Impossible"))) in
        let binders' =
          FStar_Compiler_Effect.op_Bar_Greater datas
            (FStar_Compiler_List.map
               (fun se ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu___, uu___1, t, uu___2, uu___3, uu___4) ->
                      FStar_Syntax_Syntax.null_binder t
                  | uu___ -> failwith "Impossible")) in
        let t =
          let uu___ = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
          FStar_Syntax_Util.arrow
            (FStar_Compiler_List.op_At binders binders') uu___ in
        (let uu___1 =
           FStar_Compiler_Effect.op_Less_Bar
             (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "GenUniverses") in
         if uu___1
         then
           let uu___2 = FStar_TypeChecker_Normalize.term_to_string env t in
           FStar_Compiler_Util.print1
             "@@@@@@Trying to generalize universes in %s\n" uu___2
         else ());
        (let uu___1 = FStar_TypeChecker_Generalize.generalize_universes env t in
         match uu___1 with
         | (uvs, t1) ->
             ((let uu___3 =
                 FStar_Compiler_Effect.op_Less_Bar
                   (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "GenUniverses") in
               if uu___3
               then
                 let uu___4 =
                   let uu___5 =
                     FStar_Compiler_Effect.op_Bar_Greater uvs
                       (FStar_Compiler_List.map
                          (fun u -> FStar_Ident.string_of_id u)) in
                   FStar_Compiler_Effect.op_Bar_Greater uu___5
                     (FStar_String.concat ", ") in
                 let uu___5 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Compiler_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                   uu___4 uu___5
               else ());
              (let uu___3 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
               match uu___3 with
               | (uvs1, t2) ->
                   let uu___4 = FStar_Syntax_Util.arrow_formals t2 in
                   (match uu___4 with
                    | (args, uu___5) ->
                        let uu___6 =
                          FStar_Compiler_Util.first_N
                            (FStar_Compiler_List.length binders) args in
                        (match uu___6 with
                         | (tc_types, data_types) ->
                             let tcs1 =
                               FStar_Compiler_List.map2
                                 (fun uu___7 ->
                                    fun uu___8 ->
                                      match (uu___7, uu___8) with
                                      | ({ FStar_Syntax_Syntax.binder_bv = x;
                                           FStar_Syntax_Syntax.binder_qual =
                                             uu___9;
                                           FStar_Syntax_Syntax.binder_positivity
                                             = uu___10;
                                           FStar_Syntax_Syntax.binder_attrs =
                                             uu___11;_},
                                         (se, uu___12)) ->
                                          (match se.FStar_Syntax_Syntax.sigel
                                           with
                                           | FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc, uu___13, tps,
                                                num_uniform, uu___14,
                                                mutuals, datas1)
                                               ->
                                               let ty =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs1
                                                   x.FStar_Syntax_Syntax.sort in
                                               let uu___15 =
                                                 let uu___16 =
                                                   let uu___17 =
                                                     FStar_Syntax_Subst.compress
                                                       ty in
                                                   uu___17.FStar_Syntax_Syntax.n in
                                                 match uu___16 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (binders1, c) ->
                                                     let uu___17 =
                                                       FStar_Compiler_Util.first_N
                                                         (FStar_Compiler_List.length
                                                            tps) binders1 in
                                                     (match uu___17 with
                                                      | (tps1, rest) ->
                                                          let t3 =
                                                            match rest with
                                                            | [] ->
                                                                FStar_Syntax_Util.comp_result
                                                                  c
                                                            | uu___18 ->
                                                                FStar_Syntax_Syntax.mk
                                                                  (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                  (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                          (tps1, t3))
                                                 | uu___17 -> ([], ty) in
                                               (match uu___15 with
                                                | (tps1, t3) ->
                                                    {
                                                      FStar_Syntax_Syntax.sigel
                                                        =
                                                        (FStar_Syntax_Syntax.Sig_inductive_typ
                                                           (tc, uvs1, tps1,
                                                             num_uniform, t3,
                                                             mutuals, datas1));
                                                      FStar_Syntax_Syntax.sigrng
                                                        =
                                                        (se.FStar_Syntax_Syntax.sigrng);
                                                      FStar_Syntax_Syntax.sigquals
                                                        =
                                                        (se.FStar_Syntax_Syntax.sigquals);
                                                      FStar_Syntax_Syntax.sigmeta
                                                        =
                                                        (se.FStar_Syntax_Syntax.sigmeta);
                                                      FStar_Syntax_Syntax.sigattrs
                                                        =
                                                        (se.FStar_Syntax_Syntax.sigattrs);
                                                      FStar_Syntax_Syntax.sigopts
                                                        =
                                                        (se.FStar_Syntax_Syntax.sigopts)
                                                    })
                                           | uu___13 -> failwith "Impossible"))
                                 tc_types tcs in
                             let datas1 =
                               match uvs1 with
                               | [] -> datas
                               | uu___7 ->
                                   let uvs_universes =
                                     FStar_Compiler_Effect.op_Bar_Greater
                                       uvs1
                                       (FStar_Compiler_List.map
                                          (fun uu___8 ->
                                             FStar_Syntax_Syntax.U_name
                                               uu___8)) in
                                   let tc_insts =
                                     FStar_Compiler_Effect.op_Bar_Greater
                                       tcs1
                                       (FStar_Compiler_List.map
                                          (fun uu___8 ->
                                             match uu___8 with
                                             | {
                                                 FStar_Syntax_Syntax.sigel =
                                                   FStar_Syntax_Syntax.Sig_inductive_typ
                                                   (tc, uu___9, uu___10,
                                                    uu___11, uu___12,
                                                    uu___13, uu___14);
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu___15;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = uu___16;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   = uu___17;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = uu___18;
                                                 FStar_Syntax_Syntax.sigopts
                                                   = uu___19;_}
                                                 -> (tc, uvs_universes)
                                             | uu___9 ->
                                                 failwith "Impossible")) in
                                   FStar_Compiler_List.map2
                                     (fun uu___8 ->
                                        fun d ->
                                          match uu___8 with
                                          | {
                                              FStar_Syntax_Syntax.binder_bv =
                                                t3;
                                              FStar_Syntax_Syntax.binder_qual
                                                = uu___9;
                                              FStar_Syntax_Syntax.binder_positivity
                                                = uu___10;
                                              FStar_Syntax_Syntax.binder_attrs
                                                = uu___11;_}
                                              ->
                                              (match d.FStar_Syntax_Syntax.sigel
                                               with
                                               | FStar_Syntax_Syntax.Sig_datacon
                                                   (l, uu___12, uu___13, tc,
                                                    ntps, mutuals)
                                                   ->
                                                   let ty =
                                                     let uu___14 =
                                                       FStar_Syntax_InstFV.instantiate
                                                         tc_insts
                                                         t3.FStar_Syntax_Syntax.sort in
                                                     FStar_Compiler_Effect.op_Bar_Greater
                                                       uu___14
                                                       (FStar_Syntax_Subst.close_univ_vars
                                                          uvs1) in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (l, uvs1, ty, tc,
                                                            ntps, mutuals));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (d.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (d.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (d.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (d.FStar_Syntax_Syntax.sigattrs);
                                                     FStar_Syntax_Syntax.sigopts
                                                       =
                                                       (d.FStar_Syntax_Syntax.sigopts)
                                                   }
                                               | uu___12 ->
                                                   failwith "Impossible"))
                                     data_types datas in
                             (tcs1, datas1))))))
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
      FStar_Compiler_List.op_At uu___1 uu___2 in
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
                (lid, uu___1, bs, uu___2, t, uu___3, uu___4) -> (lid, bs, t)
            | uu___1 -> failwith "Impossible!" in
          match uu___ with
          | (lid, bs, t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
              let t1 =
                let uu___1 =
                  FStar_Syntax_Subst.shift_subst
                    (FStar_Compiler_List.length bs1) usubst in
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
                       FStar_Compiler_List.map
                         (fun u -> FStar_Syntax_Syntax.U_name u) us in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu___2 uu___3 in
                   let ind1 =
                     let uu___2 =
                       FStar_Compiler_List.map
                         FStar_Syntax_Util.arg_of_non_null_binder bs2 in
                     FStar_Syntax_Syntax.mk_Tm_app ind uu___2
                       FStar_Compiler_Range_Type.dummyRange in
                   let ind2 =
                     let uu___2 =
                       FStar_Compiler_List.map
                         FStar_Syntax_Util.arg_of_non_null_binder ibs1 in
                     FStar_Syntax_Syntax.mk_Tm_app ind1 uu___2
                       FStar_Compiler_Range_Type.dummyRange in
                   let haseq_ind =
                     let uu___2 =
                       let uu___3 = FStar_Syntax_Syntax.as_arg ind2 in
                       [uu___3] in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                       uu___2 FStar_Compiler_Range_Type.dummyRange in
                   let bs' =
                     FStar_Compiler_List.filter
                       (fun b ->
                          let uu___2 =
                            let uu___3 = FStar_Syntax_Util.type_u () in
                            FStar_Pervasives_Native.fst uu___3 in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                            uu___2) bs2 in
                   let haseq_bs =
                     FStar_Compiler_List.fold_left
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
                                FStar_Compiler_Range_Type.dummyRange in
                            FStar_Syntax_Util.mk_conj t3 uu___2)
                       FStar_Syntax_Util.t_true bs' in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
                   let fml1 =
                     let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             let uu___6 =
                               FStar_Syntax_Syntax.binders_to_names ibs1 in
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind in
                                 [uu___9] in
                               [uu___8] in
                             (uu___6, uu___7) in
                           FStar_Syntax_Syntax.Meta_pattern uu___5 in
                         (fml, uu___4) in
                       FStar_Syntax_Syntax.Tm_meta uu___3 in
                     {
                       FStar_Syntax_Syntax.n = uu___2;
                       FStar_Syntax_Syntax.pos =
                         (fml.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (fml.FStar_Syntax_Syntax.vars);
                       FStar_Syntax_Syntax.hash_code =
                         (fml.FStar_Syntax_Syntax.hash_code)
                     } in
                   let fml2 =
                     FStar_Compiler_List.fold_right
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
                              FStar_Compiler_Range_Type.dummyRange) ibs1 fml1 in
                   let fml3 =
                     FStar_Compiler_List.fold_right
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
                              FStar_Compiler_Range_Type.dummyRange) bs2 fml2 in
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
                let uu___2 =
                  FStar_Compiler_List.splitAt (FStar_Compiler_List.length bs)
                    dbs in
                FStar_Pervasives_Native.snd uu___2 in
              let dbs2 =
                let uu___2 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu___2 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_Compiler_List.fold_left
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
                           FStar_Compiler_Range_Type.dummyRange in
                       let sort_range =
                         ((b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu___2 =
                           let uu___3 = FStar_Ident.string_of_lid ty_lid in
                           FStar_Compiler_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             uu___3 in
                         FStar_TypeChecker_Util.label uu___2 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_Compiler_List.fold_right
                (fun b ->
                   fun t ->
                     let uu___2 =
                       let uu___3 =
                         FStar_Syntax_Syntax.iarg
                           (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                       let uu___4 =
                         let uu___5 =
                           let uu___6 =
                             let uu___7 =
                               let uu___8 =
                                 FStar_Syntax_Syntax.mk_binder
                                   b.FStar_Syntax_Syntax.binder_bv in
                               [uu___8] in
                             let uu___8 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs uu___7 uu___8
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.as_arg uu___6 in
                         [uu___5] in
                       uu___3 :: uu___4 in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                       uu___2 FStar_Compiler_Range_Type.dummyRange) dbs3 cond
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
                  (lid1, uu___, uu___1, uu___2, uu___3, uu___4, uu___5) ->
                  lid1
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
                            FStar_Compiler_List.filter
                              (fun s ->
                                 match s.FStar_Syntax_Syntax.sigel with
                                 | FStar_Syntax_Syntax.Sig_datacon
                                     (uu___6, uu___7, uu___8, t_lid, uu___9,
                                      uu___10)
                                     -> t_lid = lid
                                 | uu___6 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_Compiler_List.fold_left
                              (fun acc1 ->
                                 fun d ->
                                   let uu___6 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs in
                                   FStar_Syntax_Util.mk_conj acc1 uu___6)
                              FStar_Syntax_Util.t_true t_datas in
                          let uu___6 = FStar_Syntax_Util.mk_conj guard' guard in
                          let uu___7 = FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_Compiler_List.op_At l_axioms
                              [(axiom_lid, fml)]), env2, uu___6, uu___7)))
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
            let ty = FStar_Compiler_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu___1, us, uu___2, uu___3, t, uu___4, uu___5) -> (us, t)
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
                       FStar_Compiler_List.fold_left
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
                                  FStar_Compiler_List.fold_left
                                    (fun l ->
                                       fun uu___8 ->
                                         match uu___8 with
                                         | (lid, fml) ->
                                             let fml1 =
                                               FStar_Syntax_Subst.close_univ_vars
                                                 us1 fml in
                                             FStar_Compiler_List.op_At l
                                               [{
                                                  FStar_Syntax_Syntax.sigel =
                                                    (FStar_Syntax_Syntax.Sig_assume
                                                       (lid, us1, fml1));
                                                  FStar_Syntax_Syntax.sigrng
                                                    =
                                                    FStar_Compiler_Range_Type.dummyRange;
                                                  FStar_Syntax_Syntax.sigquals
                                                    =
                                                    [FStar_Syntax_Syntax.InternalAssumption];
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
                    FStar_Compiler_List.existsb
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
                         FStar_Compiler_List.map FStar_Pervasives_Native.fst
                           args in
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
                      FStar_Compiler_List.splitAt
                        (FStar_Compiler_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu___2 in
                  let dbs2 =
                    let uu___2 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu___2 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_Compiler_List.fold_left
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
                               FStar_Compiler_Range_Type.dummyRange in
                           let haseq_sort1 =
                             let uu___2 = is_mutual sort in
                             if uu___2
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_Compiler_List.fold_right
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
                             FStar_Compiler_Range_Type.dummyRange) dbs3 cond in
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
                    (lid, uu___1, bs, uu___2, t, uu___3, d_lids) ->
                    (lid, bs, t, d_lids)
                | uu___1 -> failwith "Impossible!" in
              match uu___ with
              | (lid, bs, t, d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu___1 =
                      FStar_Syntax_Subst.shift_subst
                        (FStar_Compiler_List.length bs1) usubst in
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
                           FStar_Compiler_List.map
                             (fun u -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu___2 uu___3 in
                       let ind1 =
                         let uu___2 =
                           FStar_Compiler_List.map
                             FStar_Syntax_Util.arg_of_non_null_binder bs2 in
                         FStar_Syntax_Syntax.mk_Tm_app ind uu___2
                           FStar_Compiler_Range_Type.dummyRange in
                       let ind2 =
                         let uu___2 =
                           FStar_Compiler_List.map
                             FStar_Syntax_Util.arg_of_non_null_binder ibs1 in
                         FStar_Syntax_Syntax.mk_Tm_app ind1 uu___2
                           FStar_Compiler_Range_Type.dummyRange in
                       let haseq_ind =
                         let uu___2 =
                           let uu___3 = FStar_Syntax_Syntax.as_arg ind2 in
                           [uu___3] in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu___2
                           FStar_Compiler_Range_Type.dummyRange in
                       let t_datas =
                         FStar_Compiler_List.filter
                           (fun s ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu___2, uu___3, uu___4, t_lid, uu___5,
                                   uu___6)
                                  -> t_lid = lid
                              | uu___2 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_Compiler_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___2 =
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 let uu___6 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1 in
                                 let uu___7 =
                                   let uu___8 =
                                     let uu___9 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind in
                                     [uu___9] in
                                   [uu___8] in
                                 (uu___6, uu___7) in
                               FStar_Syntax_Syntax.Meta_pattern uu___5 in
                             (fml, uu___4) in
                           FStar_Syntax_Syntax.Tm_meta uu___3 in
                         {
                           FStar_Syntax_Syntax.n = uu___2;
                           FStar_Syntax_Syntax.pos =
                             (fml.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (fml.FStar_Syntax_Syntax.vars);
                           FStar_Syntax_Syntax.hash_code =
                             (fml.FStar_Syntax_Syntax.hash_code)
                         } in
                       let fml2 =
                         FStar_Compiler_List.fold_right
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
                                  FStar_Compiler_Range_Type.dummyRange) ibs1
                           fml1 in
                       let fml3 =
                         FStar_Compiler_List.fold_right
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
                                  FStar_Compiler_Range_Type.dummyRange) bs2
                           fml2 in
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
            FStar_Compiler_List.map
              (fun ty ->
                 match ty.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid, uu___, uu___1, uu___2, uu___3, uu___4, uu___5) ->
                     lid
                 | uu___ -> failwith "Impossible!") tcs in
          let uu___ =
            let ty = FStar_Compiler_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, us, uu___1, uu___2, uu___3, uu___4, uu___5) ->
                (lid, us)
            | uu___1 -> failwith "Impossible!" in
          match uu___ with
          | (lid, us) ->
              let uu___1 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu___1 with
               | (usubst, us1) ->
                   let fml =
                     FStar_Compiler_List.fold_left
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
                       FStar_Syntax_Syntax.sigrng =
                         FStar_Compiler_Range_Type.dummyRange;
                       FStar_Syntax_Syntax.sigquals =
                         [FStar_Syntax_Syntax.InternalAssumption];
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
            FStar_Compiler_Effect.op_Bar_Greater ses
              (FStar_Compiler_List.partition
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
                  FStar_Compiler_Effect.op_Bar_Greater datas
                    (FStar_Compiler_Util.for_some
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
                    (FStar_Errors_Codes.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu___3
                else ());
               (let univs =
                  if (FStar_Compiler_List.length tys) = Prims.int_zero
                  then []
                  else
                    (let uu___3 =
                       let uu___4 = FStar_Compiler_List.hd tys in
                       uu___4.FStar_Syntax_Syntax.sigel in
                     match uu___3 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu___4, uvs, uu___5, uu___6, uu___7, uu___8,
                          uu___9)
                         -> uvs
                     | uu___4 -> failwith "Impossible, can't happen!") in
                let env0 = env in
                let uu___2 =
                  FStar_Compiler_List.fold_right
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
                                      FStar_Compiler_Util.print1
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
                      FStar_Compiler_List.fold_right
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
                             FStar_Compiler_List.map
                               FStar_Pervasives_Native.snd tcs in
                           let g2 =
                             {
                               FStar_TypeChecker_Common.guard_f =
                                 (g1.FStar_TypeChecker_Common.guard_f);
                               FStar_TypeChecker_Common.deferred_to_tac =
                                 (g1.FStar_TypeChecker_Common.deferred_to_tac);
                               FStar_TypeChecker_Common.deferred =
                                 (g1.FStar_TypeChecker_Common.deferred);
                               FStar_TypeChecker_Common.univ_ineqs =
                                 (tc_universe_vars,
                                   (FStar_Pervasives_Native.snd
                                      g1.FStar_TypeChecker_Common.univ_ineqs));
                               FStar_TypeChecker_Common.implicits =
                                 (g1.FStar_TypeChecker_Common.implicits)
                             } in
                           (let uu___6 =
                              FStar_Compiler_Effect.op_Less_Bar
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "GenUniverses") in
                            if uu___6
                            then
                              let uu___7 =
                                FStar_TypeChecker_Rel.guard_to_string env1 g2 in
                              FStar_Compiler_Util.print1
                                "@@@@@@Guard before (possible) generalization: %s\n"
                                uu___7
                            else ());
                           FStar_TypeChecker_Rel.force_trivial_guard env0 g2;
                           if
                             (FStar_Compiler_List.length univs) =
                               Prims.int_zero
                           then generalize_and_inst_within env0 tcs datas1
                           else
                             (let uu___8 =
                                FStar_Compiler_List.map
                                  FStar_Pervasives_Native.fst tcs in
                              (uu___8, datas1)) in
                         (match uu___4 with
                          | (tcs1, datas2) ->
                              let tcs2 =
                                FStar_Compiler_Effect.op_Bar_Greater tcs1
                                  (FStar_Compiler_List.map
                                     (fun se ->
                                        match se.FStar_Syntax_Syntax.sigel
                                        with
                                        | FStar_Syntax_Syntax.Sig_inductive_typ
                                            (l, univs1, binders, num_uniform,
                                             typ, ts, ds)
                                            ->
                                            let fail expected inferred =
                                              let uu___5 =
                                                let uu___6 =
                                                  let uu___7 =
                                                    FStar_Syntax_Print.tscheme_to_string
                                                      expected in
                                                  let uu___8 =
                                                    FStar_Syntax_Print.tscheme_to_string
                                                      inferred in
                                                  FStar_Compiler_Util.format2
                                                    "Expected an inductive with type %s; got %s"
                                                    uu___7 uu___8 in
                                                (FStar_Errors_Codes.Fatal_UnexpectedInductivetype,
                                                  uu___6) in
                                              FStar_Errors.raise_error uu___5
                                                se.FStar_Syntax_Syntax.sigrng in
                                            let copy_binder_attrs_from_val
                                              binders1 expected =
                                              let expected_attrs =
                                                let uu___5 =
                                                  let uu___6 =
                                                    FStar_TypeChecker_Normalize.get_n_binders
                                                      env1
                                                      (FStar_Compiler_List.length
                                                         binders1) expected in
                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                    uu___6
                                                    FStar_Pervasives_Native.fst in
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  uu___5
                                                  (FStar_Compiler_List.map
                                                     (fun uu___6 ->
                                                        match uu___6 with
                                                        | {
                                                            FStar_Syntax_Syntax.binder_bv
                                                              = uu___7;
                                                            FStar_Syntax_Syntax.binder_qual
                                                              = uu___8;
                                                            FStar_Syntax_Syntax.binder_positivity
                                                              = pqual;
                                                            FStar_Syntax_Syntax.binder_attrs
                                                              = attrs;_}
                                                            -> (attrs, pqual))) in
                                              if
                                                (FStar_Compiler_List.length
                                                   expected_attrs)
                                                  <>
                                                  (FStar_Compiler_List.length
                                                     binders1)
                                              then
                                                let uu___5 =
                                                  let uu___6 =
                                                    let uu___7 =
                                                      let uu___8 =
                                                        FStar_Compiler_Effect.op_Bar_Greater
                                                          binders1
                                                          FStar_Compiler_List.length in
                                                      FStar_Compiler_Effect.op_Bar_Greater
                                                        uu___8
                                                        FStar_Compiler_Util.string_of_int in
                                                    let uu___8 =
                                                      FStar_Syntax_Print.term_to_string
                                                        expected in
                                                    FStar_Compiler_Util.format2
                                                      "Could not get %s type parameters from val type %s"
                                                      uu___7 uu___8 in
                                                  (FStar_Errors_Codes.Fatal_UnexpectedInductivetype,
                                                    uu___6) in
                                                FStar_Errors.raise_error
                                                  uu___5
                                                  se.FStar_Syntax_Syntax.sigrng
                                              else
                                                FStar_Compiler_List.map2
                                                  (fun uu___6 ->
                                                     fun b ->
                                                       match uu___6 with
                                                       | (ex_attrs, pqual) ->
                                                           ((let uu___8 =
                                                               let uu___9 =
                                                                 FStar_TypeChecker_Common.check_positivity_qual
                                                                   true pqual
                                                                   b.FStar_Syntax_Syntax.binder_positivity in
                                                               Prims.op_Negation
                                                                 uu___9 in
                                                             if uu___8
                                                             then
                                                               let uu___9 =
                                                                 FStar_Syntax_Syntax.range_of_bv
                                                                   b.FStar_Syntax_Syntax.binder_bv in
                                                               FStar_Errors.raise_error
                                                                 (FStar_Errors_Codes.Fatal_UnexpectedInductivetype,
                                                                   "Incompatible positivity annotation")
                                                                 uu___9
                                                             else ());
                                                            {
                                                              FStar_Syntax_Syntax.binder_bv
                                                                =
                                                                (b.FStar_Syntax_Syntax.binder_bv);
                                                              FStar_Syntax_Syntax.binder_qual
                                                                =
                                                                (b.FStar_Syntax_Syntax.binder_qual);
                                                              FStar_Syntax_Syntax.binder_positivity
                                                                = pqual;
                                                              FStar_Syntax_Syntax.binder_attrs
                                                                =
                                                                (FStar_Compiler_List.op_At
                                                                   b.FStar_Syntax_Syntax.binder_attrs
                                                                   ex_attrs)
                                                            }))
                                                  expected_attrs binders1 in
                                            let inferred_typ_with_binders
                                              binders1 =
                                              let body =
                                                match binders1 with
                                                | [] -> typ
                                                | uu___5 ->
                                                    let uu___6 =
                                                      let uu___7 =
                                                        let uu___8 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            typ in
                                                        (binders1, uu___8) in
                                                      FStar_Syntax_Syntax.Tm_arrow
                                                        uu___7 in
                                                    FStar_Syntax_Syntax.mk
                                                      uu___6
                                                      se.FStar_Syntax_Syntax.sigrng in
                                              (univs1, body) in
                                            let uu___5 =
                                              FStar_TypeChecker_Env.try_lookup_val_decl
                                                env0 l in
                                            (match uu___5 with
                                             | FStar_Pervasives_Native.None
                                                 -> se
                                             | FStar_Pervasives_Native.Some
                                                 (expected_typ, uu___6) ->
                                                 if
                                                   (FStar_Compiler_List.length
                                                      univs1)
                                                     =
                                                     (FStar_Compiler_List.length
                                                        (FStar_Pervasives_Native.fst
                                                           expected_typ))
                                                 then
                                                   let uu___7 =
                                                     FStar_Syntax_Subst.open_univ_vars
                                                       univs1
                                                       (FStar_Pervasives_Native.snd
                                                          expected_typ) in
                                                   (match uu___7 with
                                                    | (uu___8, expected) ->
                                                        let binders1 =
                                                          copy_binder_attrs_from_val
                                                            binders expected in
                                                        let inferred_typ =
                                                          inferred_typ_with_binders
                                                            binders1 in
                                                        let uu___9 =
                                                          FStar_Syntax_Subst.open_univ_vars
                                                            univs1
                                                            (FStar_Pervasives_Native.snd
                                                               inferred_typ) in
                                                        (match uu___9 with
                                                         | (uu___10,
                                                            inferred) ->
                                                             let uu___11 =
                                                               FStar_TypeChecker_Rel.teq_nosmt_force
                                                                 env0
                                                                 inferred
                                                                 expected in
                                                             if uu___11
                                                             then
                                                               {
                                                                 FStar_Syntax_Syntax.sigel
                                                                   =
                                                                   (FStar_Syntax_Syntax.Sig_inductive_typ
                                                                    (l,
                                                                    univs1,
                                                                    binders1,
                                                                    num_uniform,
                                                                    typ, ts,
                                                                    ds));
                                                                 FStar_Syntax_Syntax.sigrng
                                                                   =
                                                                   (se.FStar_Syntax_Syntax.sigrng);
                                                                 FStar_Syntax_Syntax.sigquals
                                                                   =
                                                                   (se.FStar_Syntax_Syntax.sigquals);
                                                                 FStar_Syntax_Syntax.sigmeta
                                                                   =
                                                                   (se.FStar_Syntax_Syntax.sigmeta);
                                                                 FStar_Syntax_Syntax.sigattrs
                                                                   =
                                                                   (se.FStar_Syntax_Syntax.sigattrs);
                                                                 FStar_Syntax_Syntax.sigopts
                                                                   =
                                                                   (se.FStar_Syntax_Syntax.sigopts)
                                                               }
                                                             else
                                                               fail
                                                                 expected_typ
                                                                 inferred_typ))
                                                 else
                                                   (let uu___8 =
                                                      inferred_typ_with_binders
                                                        binders in
                                                    fail expected_typ uu___8))
                                        | uu___5 -> se)) in
                              let sig_bndle =
                                let uu___5 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                let uu___6 =
                                  FStar_Compiler_List.collect
                                    (fun s -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_Compiler_List.op_At tcs2
                                           datas2), lids));
                                  FStar_Syntax_Syntax.sigrng = uu___5;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu___6;
                                  FStar_Syntax_Syntax.sigopts =
                                    FStar_Pervasives_Native.None
                                } in
                              (sig_bndle, tcs2, datas2)))))
let (early_prims_inductives : Prims.string Prims.list) =
  ["empty"; "trivial"; "equals"; "pair"; "sum"]
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
                            FStar_Compiler_List.map
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
                              FStar_Compiler_Effect.op_Bar_Greater
                                (FStar_Compiler_List.op_At tps indices)
                                (FStar_Compiler_List.map
                                   FStar_Syntax_Util.arg_of_non_null_binder) in
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
                                         FStar_Compiler_Effect.op_Less_Bar
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
                          let ntps = FStar_Compiler_List.length tps in
                          let all_params =
                            let uu___ =
                              FStar_Compiler_List.map
                                (fun b ->
                                   {
                                     FStar_Syntax_Syntax.binder_bv =
                                       (b.FStar_Syntax_Syntax.binder_bv);
                                     FStar_Syntax_Syntax.binder_qual =
                                       (FStar_Pervasives_Native.Some
                                          FStar_Syntax_Syntax.imp_tag);
                                     FStar_Syntax_Syntax.binder_positivity =
                                       (b.FStar_Syntax_Syntax.binder_positivity);
                                     FStar_Syntax_Syntax.binder_attrs =
                                       (b.FStar_Syntax_Syntax.binder_attrs)
                                   }) tps in
                            FStar_Compiler_List.op_At uu___ fields in
                          let imp_binders =
                            FStar_Compiler_Effect.op_Bar_Greater
                              (FStar_Compiler_List.op_At tps indices)
                              (FStar_Compiler_List.map
                                 (fun b ->
                                    {
                                      FStar_Syntax_Syntax.binder_bv =
                                        (b.FStar_Syntax_Syntax.binder_bv);
                                      FStar_Syntax_Syntax.binder_qual =
                                        (FStar_Pervasives_Native.Some
                                           FStar_Syntax_Syntax.imp_tag);
                                      FStar_Syntax_Syntax.binder_positivity =
                                        (b.FStar_Syntax_Syntax.binder_positivity);
                                      FStar_Syntax_Syntax.binder_attrs =
                                        (b.FStar_Syntax_Syntax.binder_attrs)
                                    })) in
                          let early_prims_inductive =
                            (let uu___ =
                               FStar_TypeChecker_Env.current_module env in
                             FStar_Ident.lid_equals
                               FStar_Parser_Const.prims_lid uu___)
                              &&
                              (FStar_Compiler_List.existsb
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
                                   (FStar_Syntax_Util.has_attribute attrs
                                      FStar_Parser_Const.no_auto_projectors_attr) in
                               let quals =
                                 let uu___1 =
                                   FStar_Compiler_List.filter
                                     (fun uu___2 ->
                                        match uu___2 with
                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                            -> true
                                        | FStar_Syntax_Syntax.NoExtract ->
                                            true
                                        | FStar_Syntax_Syntax.Private -> true
                                        | uu___3 -> false) iquals in
                                 FStar_Compiler_List.op_At
                                   ((FStar_Syntax_Syntax.Discriminator lid)
                                   ::
                                   (if only_decl
                                    then
                                      [FStar_Syntax_Syntax.Logic;
                                      FStar_Syntax_Syntax.Assumption]
                                    else [])) uu___1 in
                               let binders =
                                 FStar_Compiler_List.op_At imp_binders
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
                                 FStar_Compiler_Effect.op_Less_Bar
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
                                  FStar_Compiler_Util.print1
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
                                         FStar_Compiler_Effect.op_Bar_Greater
                                           all_params
                                           (FStar_Compiler_List.mapi
                                              (fun j ->
                                                 fun uu___4 ->
                                                   match uu___4 with
                                                   | {
                                                       FStar_Syntax_Syntax.binder_bv
                                                         = x;
                                                       FStar_Syntax_Syntax.binder_qual
                                                         = imp;
                                                       FStar_Syntax_Syntax.binder_positivity
                                                         = uu___5;
                                                       FStar_Syntax_Syntax.binder_attrs
                                                         = uu___6;_}
                                                       ->
                                                       let b =
                                                         FStar_Syntax_Syntax.is_bqual_implicit
                                                           imp in
                                                       if b && (j < ntps)
                                                       then
                                                         let uu___7 =
                                                           pos
                                                             (FStar_Syntax_Syntax.Pat_dot_term
                                                                FStar_Pervasives_Native.None) in
                                                         (uu___7, b)
                                                       else
                                                         (let uu___8 =
                                                            let uu___9 =
                                                              let uu___10 =
                                                                let uu___11 =
                                                                  FStar_Ident.string_of_id
                                                                    x.FStar_Syntax_Syntax.ppname in
                                                                FStar_Syntax_Syntax.gen_bv
                                                                  uu___11
                                                                  FStar_Pervasives_Native.None
                                                                  FStar_Syntax_Syntax.tun in
                                                              FStar_Syntax_Syntax.Pat_wild
                                                                uu___10 in
                                                            pos uu___9 in
                                                          (uu___8, b)))) in
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
                                               (uu___7,
                                                 FStar_Pervasives_Native.None,
                                                 arg_pats) in
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
                                             uu___6,
                                             FStar_Pervasives_Native.None) in
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
                                      uu___4 []
                                      FStar_Compiler_Range_Type.dummyRange in
                                  let impl =
                                    let uu___3 =
                                      let uu___4 =
                                        let uu___5 =
                                          let uu___6 =
                                            let uu___7 =
                                              FStar_Compiler_Effect.op_Bar_Greater
                                                lb.FStar_Syntax_Syntax.lbname
                                                FStar_Compiler_Util.right in
                                            FStar_Compiler_Effect.op_Bar_Greater
                                              uu___7
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
                                     FStar_Compiler_Util.print1
                                       "Implementation of a discriminator %s\n"
                                       uu___5
                                   else ());
                                  [decl; impl])) in
                          let arg_exp =
                            FStar_Syntax_Syntax.bv_to_name
                              arg_binder.FStar_Syntax_Syntax.binder_bv in
                          let binders =
                            FStar_Compiler_List.op_At imp_binders
                              [arg_binder] in
                          let arg =
                            FStar_Syntax_Util.arg_of_non_null_binder
                              arg_binder in
                          let subst =
                            FStar_Compiler_Effect.op_Bar_Greater fields
                              (FStar_Compiler_List.mapi
                                 (fun i ->
                                    fun uu___ ->
                                      match uu___ with
                                      | { FStar_Syntax_Syntax.binder_bv = a;
                                          FStar_Syntax_Syntax.binder_qual =
                                            uu___1;
                                          FStar_Syntax_Syntax.binder_positivity
                                            = uu___2;
                                          FStar_Syntax_Syntax.binder_attrs =
                                            uu___3;_}
                                          ->
                                          let field_name =
                                            FStar_Syntax_Util.mk_field_projector_name
                                              lid a i in
                                          let field_proj_tm =
                                            let uu___4 =
                                              let uu___5 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  field_name
                                                  (FStar_Syntax_Syntax.Delta_equational_at_level
                                                     Prims.int_one)
                                                  FStar_Pervasives_Native.None in
                                              FStar_Syntax_Syntax.fv_to_tm
                                                uu___5 in
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              uu___4 inst_univs in
                                          let proj =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              field_proj_tm [arg] p in
                                          FStar_Syntax_Syntax.NT (a, proj))) in
                          let projectors_ses =
                            let uu___ =
                              FStar_Compiler_Effect.op_Bar_Greater fields
                                (FStar_Compiler_List.mapi
                                   (fun i ->
                                      fun uu___1 ->
                                        match uu___1 with
                                        | {
                                            FStar_Syntax_Syntax.binder_bv = x;
                                            FStar_Syntax_Syntax.binder_qual =
                                              uu___2;
                                            FStar_Syntax_Syntax.binder_positivity
                                              = uu___3;
                                            FStar_Syntax_Syntax.binder_attrs
                                              = uu___4;_}
                                            ->
                                            let p1 =
                                              FStar_Syntax_Syntax.range_of_bv
                                                x in
                                            let field_name =
                                              FStar_Syntax_Util.mk_field_projector_name
                                                lid x i in
                                            let result_comp =
                                              let t =
                                                FStar_Syntax_Subst.subst
                                                  subst
                                                  x.FStar_Syntax_Syntax.sort in
                                              if erasable
                                              then
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                              else
                                                FStar_Syntax_Syntax.mk_Total
                                                  t in
                                            let t =
                                              let uu___5 =
                                                FStar_Syntax_Util.arrow
                                                  binders result_comp in
                                              FStar_Compiler_Effect.op_Less_Bar
                                                (FStar_Syntax_Subst.close_univ_vars
                                                   uvs) uu___5 in
                                            let only_decl =
                                              early_prims_inductive ||
                                                (FStar_Syntax_Util.has_attribute
                                                   attrs
                                                   FStar_Parser_Const.no_auto_projectors_attr) in
                                            let no_decl = false in
                                            let quals q =
                                              if only_decl
                                              then
                                                FStar_Syntax_Syntax.Assumption
                                                :: q
                                              else q in
                                            let quals1 =
                                              let iquals1 =
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  iquals
                                                  (FStar_Compiler_List.filter
                                                     (fun uu___5 ->
                                                        match uu___5 with
                                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                                            -> true
                                                        | FStar_Syntax_Syntax.NoExtract
                                                            -> true
                                                        | FStar_Syntax_Syntax.Private
                                                            -> true
                                                        | uu___6 -> false)) in
                                              quals
                                                ((FStar_Syntax_Syntax.Projector
                                                    (lid,
                                                      (x.FStar_Syntax_Syntax.ppname)))
                                                :: iquals1) in
                                            let attrs1 =
                                              FStar_Compiler_List.op_At
                                                (if only_decl
                                                 then []
                                                 else
                                                   [FStar_Syntax_Util.attr_substitute])
                                                attrs in
                                            let decl =
                                              let uu___5 =
                                                FStar_Ident.range_of_lid
                                                  field_name in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                                     (field_name, uvs, t));
                                                FStar_Syntax_Syntax.sigrng =
                                                  uu___5;
                                                FStar_Syntax_Syntax.sigquals
                                                  = quals1;
                                                FStar_Syntax_Syntax.sigmeta =
                                                  FStar_Syntax_Syntax.default_sigmeta;
                                                FStar_Syntax_Syntax.sigattrs
                                                  = attrs1;
                                                FStar_Syntax_Syntax.sigopts =
                                                  FStar_Pervasives_Native.None
                                              } in
                                            ((let uu___6 =
                                                FStar_TypeChecker_Env.debug
                                                  env
                                                  (FStar_Options.Other
                                                     "LogTypes") in
                                              if uu___6
                                              then
                                                let uu___7 =
                                                  FStar_Syntax_Print.sigelt_to_string
                                                    decl in
                                                FStar_Compiler_Util.print1
                                                  "Declaration of a projector %s\n"
                                                  uu___7
                                              else ());
                                             if only_decl
                                             then [decl]
                                             else
                                               (let projection =
                                                  let uu___7 =
                                                    FStar_Ident.string_of_id
                                                      x.FStar_Syntax_Syntax.ppname in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    uu___7
                                                    FStar_Pervasives_Native.None
                                                    FStar_Syntax_Syntax.tun in
                                                let arg_pats =
                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                    all_params
                                                    (FStar_Compiler_List.mapi
                                                       (fun j ->
                                                          fun uu___7 ->
                                                            match uu___7 with
                                                            | {
                                                                FStar_Syntax_Syntax.binder_bv
                                                                  = x1;
                                                                FStar_Syntax_Syntax.binder_qual
                                                                  = imp;
                                                                FStar_Syntax_Syntax.binder_positivity
                                                                  = uu___8;
                                                                FStar_Syntax_Syntax.binder_attrs
                                                                  = uu___9;_}
                                                                ->
                                                                let b =
                                                                  FStar_Syntax_Syntax.is_bqual_implicit
                                                                    imp in
                                                                if
                                                                  (i + ntps)
                                                                    = j
                                                                then
                                                                  let uu___10
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                  (uu___10,
                                                                    b)
                                                                else
                                                                  if
                                                                    b &&
                                                                    (j < ntps)
                                                                  then
                                                                    (
                                                                    let uu___11
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    FStar_Pervasives_Native.None) in
                                                                    (uu___11,
                                                                    b))
                                                                  else
                                                                    (
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    x1.FStar_Syntax_Syntax.ppname in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    uu___15
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu___14 in
                                                                    pos
                                                                    uu___13 in
                                                                    (uu___12,
                                                                    b)))) in
                                                let pat =
                                                  let uu___7 =
                                                    let uu___8 =
                                                      let uu___9 =
                                                        let uu___10 =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            lid
                                                            FStar_Syntax_Syntax.delta_constant
                                                            (FStar_Pervasives_Native.Some
                                                               fvq) in
                                                        (uu___10,
                                                          FStar_Pervasives_Native.None,
                                                          arg_pats) in
                                                      FStar_Syntax_Syntax.Pat_cons
                                                        uu___9 in
                                                    pos uu___8 in
                                                  let uu___8 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      projection in
                                                  (uu___7,
                                                    FStar_Pervasives_Native.None,
                                                    uu___8) in
                                                let body =
                                                  let return_bv =
                                                    FStar_Syntax_Syntax.gen_bv
                                                      "proj_ret"
                                                      (FStar_Pervasives_Native.Some
                                                         p1)
                                                      FStar_Syntax_Syntax.tun in
                                                  let result_typ =
                                                    let uu___7 =
                                                      let uu___8 =
                                                        FStar_Compiler_Effect.op_Bar_Greater
                                                          result_comp
                                                          FStar_Syntax_Util.comp_result in
                                                      let uu___9 =
                                                        let uu___10 =
                                                          let uu___11 =
                                                            let uu___12 =
                                                              let uu___13 =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  return_bv in
                                                              ((arg_binder.FStar_Syntax_Syntax.binder_bv),
                                                                uu___13) in
                                                            FStar_Syntax_Syntax.NT
                                                              uu___12 in
                                                          [uu___11] in
                                                        FStar_Syntax_Subst.subst
                                                          uu___10 in
                                                      FStar_Compiler_Effect.op_Bar_Greater
                                                        uu___8 uu___9 in
                                                    let uu___8 =
                                                      let uu___9 =
                                                        let uu___10 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            return_bv in
                                                        [uu___10] in
                                                      FStar_Syntax_Subst.close
                                                        uu___9 in
                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                      uu___7 uu___8 in
                                                  let return_binder =
                                                    let uu___7 =
                                                      let uu___8 =
                                                        let uu___9 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            return_bv in
                                                        [uu___9] in
                                                      FStar_Syntax_Subst.close_binders
                                                        uu___8 in
                                                    FStar_Compiler_List.hd
                                                      uu___7 in
                                                  let returns_annotation =
                                                    let use_eq = true in
                                                    FStar_Pervasives_Native.Some
                                                      (return_binder,
                                                        ((FStar_Pervasives.Inl
                                                            result_typ),
                                                          FStar_Pervasives_Native.None,
                                                          use_eq)) in
                                                  let uu___7 =
                                                    let uu___8 =
                                                      let uu___9 =
                                                        let uu___10 =
                                                          FStar_Syntax_Util.branch
                                                            pat in
                                                        [uu___10] in
                                                      (arg_exp,
                                                        returns_annotation,
                                                        uu___9,
                                                        FStar_Pervasives_Native.None) in
                                                    FStar_Syntax_Syntax.Tm_match
                                                      uu___8 in
                                                  FStar_Syntax_Syntax.mk
                                                    uu___7 p1 in
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
                                                  let uu___7 =
                                                    let uu___8 =
                                                      FStar_Syntax_Syntax.lid_as_fv
                                                        field_name dd
                                                        FStar_Pervasives_Native.None in
                                                    FStar_Pervasives.Inr
                                                      uu___8 in
                                                  let uu___8 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs imp in
                                                  {
                                                    FStar_Syntax_Syntax.lbname
                                                      = uu___7;
                                                    FStar_Syntax_Syntax.lbunivs
                                                      = uvs;
                                                    FStar_Syntax_Syntax.lbtyp
                                                      = lbtyp;
                                                    FStar_Syntax_Syntax.lbeff
                                                      =
                                                      FStar_Parser_Const.effect_Tot_lid;
                                                    FStar_Syntax_Syntax.lbdef
                                                      = uu___8;
                                                    FStar_Syntax_Syntax.lbattrs
                                                      = [];
                                                    FStar_Syntax_Syntax.lbpos
                                                      =
                                                      FStar_Compiler_Range_Type.dummyRange
                                                  } in
                                                let impl =
                                                  let uu___7 =
                                                    let uu___8 =
                                                      let uu___9 =
                                                        let uu___10 =
                                                          let uu___11 =
                                                            FStar_Compiler_Effect.op_Bar_Greater
                                                              lb.FStar_Syntax_Syntax.lbname
                                                              FStar_Compiler_Util.right in
                                                          FStar_Compiler_Effect.op_Bar_Greater
                                                            uu___11
                                                            (fun fv ->
                                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                        [uu___10] in
                                                      ((false, [lb]), uu___9) in
                                                    FStar_Syntax_Syntax.Sig_let
                                                      uu___8 in
                                                  {
                                                    FStar_Syntax_Syntax.sigel
                                                      = uu___7;
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
                                                (let uu___8 =
                                                   FStar_TypeChecker_Env.debug
                                                     env
                                                     (FStar_Options.Other
                                                        "LogTypes") in
                                                 if uu___8
                                                 then
                                                   let uu___9 =
                                                     FStar_Syntax_Print.sigelt_to_string
                                                       impl in
                                                   FStar_Compiler_Util.print1
                                                     "Implementation of a projector %s\n"
                                                     uu___9
                                                 else ());
                                                if no_decl
                                                then [impl]
                                                else [decl; impl])))) in
                            FStar_Compiler_Effect.op_Bar_Greater uu___
                              FStar_Compiler_List.flatten in
                          FStar_Compiler_List.op_At discriminator_ses
                            projectors_ses
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
                              FStar_Compiler_Util.find_map tcs
                                (fun se1 ->
                                   let uu___5 =
                                     let uu___6 =
                                       let uu___7 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Compiler_Util.must uu___7 in
                                     FStar_Ident.lid_equals typ_lid uu___6 in
                                   if uu___5
                                   then
                                     match se1.FStar_Syntax_Syntax.sigel with
                                     | FStar_Syntax_Syntax.Sig_inductive_typ
                                         (uu___6, uvs', tps, uu___7, typ0,
                                          uu___8, constrs)
                                         ->
                                         FStar_Pervasives_Native.Some
                                           (tps, typ0,
                                             ((FStar_Compiler_List.length
                                                 constrs)
                                                > Prims.int_one))
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
                                    (FStar_Errors_Codes.Fatal_UnexpectedDataConstructor,
                                      "Unexpected data constructor")
                                    se.FStar_Syntax_Syntax.sigrng in
                          (match uu___4 with
                           | (inductive_tps, typ0, should_refine) ->
                               let inductive_tps1 =
                                 FStar_Syntax_Subst.subst_binders
                                   univ_opening inductive_tps in
                               let typ01 =
                                 let uu___5 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_Compiler_List.length
                                        inductive_tps1) univ_opening in
                                 FStar_Syntax_Subst.subst uu___5 typ0 in
                               let uu___5 =
                                 FStar_Syntax_Util.arrow_formals typ01 in
                               (match uu___5 with
                                | (indices, uu___6) ->
                                    let refine_domain =
                                      let uu___7 =
                                        FStar_Compiler_Effect.op_Bar_Greater
                                          se.FStar_Syntax_Syntax.sigquals
                                          (FStar_Compiler_Util.for_some
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
                                        FStar_Compiler_Util.find_map
                                          se.FStar_Syntax_Syntax.sigquals
                                          filter_records in
                                      match uu___7 with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Syntax_Syntax.Data_ctor
                                      | FStar_Pervasives_Native.Some q -> q in
                                    let fields =
                                      let uu___7 =
                                        FStar_Compiler_Util.first_N n_typars
                                          formals in
                                      match uu___7 with
                                      | (imp_tps, fields1) ->
                                          let rename =
                                            FStar_Compiler_List.map2
                                              (fun uu___8 ->
                                                 fun uu___9 ->
                                                   match (uu___8, uu___9)
                                                   with
                                                   | ({
                                                        FStar_Syntax_Syntax.binder_bv
                                                          = x;
                                                        FStar_Syntax_Syntax.binder_qual
                                                          = uu___10;
                                                        FStar_Syntax_Syntax.binder_positivity
                                                          = uu___11;
                                                        FStar_Syntax_Syntax.binder_attrs
                                                          = uu___12;_},
                                                      {
                                                        FStar_Syntax_Syntax.binder_bv
                                                          = x';
                                                        FStar_Syntax_Syntax.binder_qual
                                                          = uu___13;
                                                        FStar_Syntax_Syntax.binder_positivity
                                                          = uu___14;
                                                        FStar_Syntax_Syntax.binder_attrs
                                                          = uu___15;_})
                                                       ->
                                                       let uu___16 =
                                                         let uu___17 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x' in
                                                         (x, uu___17) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu___16) imp_tps
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