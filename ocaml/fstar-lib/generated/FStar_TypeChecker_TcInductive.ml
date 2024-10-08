open Prims
let (dbg_GenUniverses : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Debug.get_toggle "GenUniverses"
let (dbg_LogTypes : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Debug.get_toggle "LogTypes"
let (dbg_Injectivity : Prims.bool FStar_Compiler_Effect.ref) =
  FStar_Compiler_Debug.get_toggle "Injectivity"
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.unfold_whnf'
    [FStar_TypeChecker_Env.AllowUnboundUniverses]
let (check_sig_inductive_injectivity_on_params :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun tcenv ->
    fun se ->
      if tcenv.FStar_TypeChecker_Env.phase1
      then se
      else
        (let uu___1 = se.FStar_Syntax_Syntax.sigel in
         match uu___1 with
         | FStar_Syntax_Syntax.Sig_inductive_typ dd ->
             let uu___2 = dd in
             (match uu___2 with
              | { FStar_Syntax_Syntax.lid = t;
                  FStar_Syntax_Syntax.us = universe_names;
                  FStar_Syntax_Syntax.params = tps;
                  FStar_Syntax_Syntax.num_uniform_params = uu___3;
                  FStar_Syntax_Syntax.t = k;
                  FStar_Syntax_Syntax.mutuals = uu___4;
                  FStar_Syntax_Syntax.ds = uu___5;
                  FStar_Syntax_Syntax.injective_type_params = uu___6;_} ->
                  let t_lid = t in
                  let uu___7 =
                    FStar_Syntax_Subst.univ_var_opening universe_names in
                  (match uu___7 with
                   | (usubst, uvs) ->
                       let uu___8 =
                         let uu___9 =
                           FStar_TypeChecker_Env.push_univ_vars tcenv uvs in
                         let uu___10 =
                           FStar_Syntax_Subst.subst_binders usubst tps in
                         let uu___11 =
                           let uu___12 =
                             FStar_Syntax_Subst.shift_subst
                               (FStar_Compiler_List.length tps) usubst in
                           FStar_Syntax_Subst.subst uu___12 k in
                         (uu___9, uu___10, uu___11) in
                       (match uu___8 with
                        | (tcenv1, tps1, k1) ->
                            let uu___9 = FStar_Syntax_Subst.open_term tps1 k1 in
                            (match uu___9 with
                             | (tps2, k2) ->
                                 let uu___10 =
                                   FStar_Syntax_Util.arrow_formals k2 in
                                 (match uu___10 with
                                  | (uu___11, k3) ->
                                      let uu___12 =
                                        FStar_TypeChecker_TcTerm.tc_binders
                                          tcenv1 tps2 in
                                      (match uu___12 with
                                       | (tps3, env_tps, uu___13, us) ->
                                           let u_k =
                                             let uu___14 =
                                               let uu___15 =
                                                 FStar_Syntax_Syntax.fvar t
                                                   FStar_Pervasives_Native.None in
                                               let uu___16 =
                                                 let uu___17 =
                                                   FStar_Syntax_Util.args_of_binders
                                                     tps3 in
                                                 FStar_Pervasives_Native.snd
                                                   uu___17 in
                                               let uu___17 =
                                                 FStar_Ident.range_of_lid t in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu___15 uu___16 uu___17 in
                                             FStar_TypeChecker_TcTerm.level_of_type
                                               env_tps uu___14 k3 in
                                           let rec universe_leq u v =
                                             match (u, v) with
                                             | (FStar_Syntax_Syntax.U_zero,
                                                uu___14) -> true
                                             | (FStar_Syntax_Syntax.U_succ
                                                u0,
                                                FStar_Syntax_Syntax.U_succ
                                                v0) -> universe_leq u0 v0
                                             | (FStar_Syntax_Syntax.U_name
                                                u0,
                                                FStar_Syntax_Syntax.U_name
                                                v0) ->
                                                 FStar_Ident.ident_equals u0
                                                   v0
                                             | (FStar_Syntax_Syntax.U_name
                                                uu___14,
                                                FStar_Syntax_Syntax.U_succ
                                                v0) -> universe_leq u v0
                                             | (FStar_Syntax_Syntax.U_max
                                                us1, uu___14) ->
                                                 FStar_Compiler_Util.for_all
                                                   (fun u1 ->
                                                      universe_leq u1 v) us1
                                             | (uu___14,
                                                FStar_Syntax_Syntax.U_max vs)
                                                 ->
                                                 FStar_Compiler_Util.for_some
                                                   (universe_leq u) vs
                                             | (FStar_Syntax_Syntax.U_unknown,
                                                uu___14) ->
                                                 let uu___15 =
                                                   let uu___16 =
                                                     FStar_Class_Show.show
                                                       FStar_Ident.showable_lident
                                                       t in
                                                   let uu___17 =
                                                     FStar_Class_Show.show
                                                       FStar_Syntax_Print.showable_univ
                                                       u in
                                                   let uu___18 =
                                                     FStar_Class_Show.show
                                                       FStar_Syntax_Print.showable_univ
                                                       v in
                                                   FStar_Compiler_Util.format3
                                                     "Impossible: Unresolved or unknown universe in inductive type %s (%s, %s)"
                                                     uu___16 uu___17 uu___18 in
                                                 failwith uu___15
                                             | (uu___14,
                                                FStar_Syntax_Syntax.U_unknown)
                                                 ->
                                                 let uu___15 =
                                                   let uu___16 =
                                                     FStar_Class_Show.show
                                                       FStar_Ident.showable_lident
                                                       t in
                                                   let uu___17 =
                                                     FStar_Class_Show.show
                                                       FStar_Syntax_Print.showable_univ
                                                       u in
                                                   let uu___18 =
                                                     FStar_Class_Show.show
                                                       FStar_Syntax_Print.showable_univ
                                                       v in
                                                   FStar_Compiler_Util.format3
                                                     "Impossible: Unresolved or unknown universe in inductive type %s (%s, %s)"
                                                     uu___16 uu___17 uu___18 in
                                                 failwith uu___15
                                             | (FStar_Syntax_Syntax.U_unif
                                                uu___14, uu___15) ->
                                                 let uu___16 =
                                                   let uu___17 =
                                                     FStar_Class_Show.show
                                                       FStar_Ident.showable_lident
                                                       t in
                                                   let uu___18 =
                                                     FStar_Class_Show.show
                                                       FStar_Syntax_Print.showable_univ
                                                       u in
                                                   let uu___19 =
                                                     FStar_Class_Show.show
                                                       FStar_Syntax_Print.showable_univ
                                                       v in
                                                   FStar_Compiler_Util.format3
                                                     "Impossible: Unresolved or unknown universe in inductive type %s (%s, %s)"
                                                     uu___17 uu___18 uu___19 in
                                                 failwith uu___16
                                             | (uu___14,
                                                FStar_Syntax_Syntax.U_unif
                                                uu___15) ->
                                                 let uu___16 =
                                                   let uu___17 =
                                                     FStar_Class_Show.show
                                                       FStar_Ident.showable_lident
                                                       t in
                                                   let uu___18 =
                                                     FStar_Class_Show.show
                                                       FStar_Syntax_Print.showable_univ
                                                       u in
                                                   let uu___19 =
                                                     FStar_Class_Show.show
                                                       FStar_Syntax_Print.showable_univ
                                                       v in
                                                   FStar_Compiler_Util.format3
                                                     "Impossible: Unresolved or unknown universe in inductive type %s (%s, %s)"
                                                     uu___17 uu___18 uu___19 in
                                                 failwith uu___16
                                             | uu___14 -> false in
                                           let u_leq_u_k u =
                                             let u1 =
                                               FStar_TypeChecker_Normalize.normalize_universe
                                                 env_tps u in
                                             universe_leq u1 u_k in
                                           let tp_ok tp u_tp =
                                             let t_tp =
                                               (tp.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                             let uu___14 = u_leq_u_k u_tp in
                                             if uu___14
                                             then true
                                             else
                                               (let t_tp1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Unrefine;
                                                    FStar_TypeChecker_Env.Unascribe;
                                                    FStar_TypeChecker_Env.Unmeta;
                                                    FStar_TypeChecker_Env.Primops;
                                                    FStar_TypeChecker_Env.HNF;
                                                    FStar_TypeChecker_Env.UnfoldUntil
                                                      FStar_Syntax_Syntax.delta_constant;
                                                    FStar_TypeChecker_Env.Beta]
                                                    env_tps t_tp in
                                                let uu___16 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    t_tp1 in
                                                match uu___16 with
                                                | (formals, t1) ->
                                                    let uu___17 =
                                                      FStar_TypeChecker_TcTerm.tc_binders
                                                        env_tps formals in
                                                    (match uu___17 with
                                                     | (uu___18, uu___19,
                                                        uu___20, u_formals)
                                                         ->
                                                         let inj =
                                                           FStar_Compiler_Util.for_all
                                                             (fun u_formal ->
                                                                u_leq_u_k
                                                                  u_formal)
                                                             u_formals in
                                                         if inj
                                                         then
                                                           let uu___21 =
                                                             let uu___22 =
                                                               FStar_Syntax_Subst.compress
                                                                 t1 in
                                                             uu___22.FStar_Syntax_Syntax.n in
                                                           (match uu___21
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_type
                                                                u ->
                                                                u_leq_u_k u
                                                            | uu___22 ->
                                                                false)
                                                         else false)) in
                                           let injective_type_params =
                                             FStar_Compiler_List.forall2
                                               tp_ok tps3 us in
                                           ((let uu___15 =
                                               FStar_Compiler_Effect.op_Bang
                                                 dbg_Injectivity in
                                             if uu___15
                                             then
                                               let uu___16 =
                                                 FStar_Ident.string_of_lid t in
                                               FStar_Compiler_Util.print2
                                                 "%s injectivity for %s\n"
                                                 (if injective_type_params
                                                  then "YES"
                                                  else "NO") uu___16
                                             else ());
                                            {
                                              FStar_Syntax_Syntax.sigel =
                                                (FStar_Syntax_Syntax.Sig_inductive_typ
                                                   {
                                                     FStar_Syntax_Syntax.lid
                                                       =
                                                       (dd.FStar_Syntax_Syntax.lid);
                                                     FStar_Syntax_Syntax.us =
                                                       (dd.FStar_Syntax_Syntax.us);
                                                     FStar_Syntax_Syntax.params
                                                       =
                                                       (dd.FStar_Syntax_Syntax.params);
                                                     FStar_Syntax_Syntax.num_uniform_params
                                                       =
                                                       (dd.FStar_Syntax_Syntax.num_uniform_params);
                                                     FStar_Syntax_Syntax.t =
                                                       (dd.FStar_Syntax_Syntax.t);
                                                     FStar_Syntax_Syntax.mutuals
                                                       =
                                                       (dd.FStar_Syntax_Syntax.mutuals);
                                                     FStar_Syntax_Syntax.ds =
                                                       (dd.FStar_Syntax_Syntax.ds);
                                                     FStar_Syntax_Syntax.injective_type_params
                                                       =
                                                       injective_type_params
                                                   });
                                              FStar_Syntax_Syntax.sigrng =
                                                (se.FStar_Syntax_Syntax.sigrng);
                                              FStar_Syntax_Syntax.sigquals =
                                                (se.FStar_Syntax_Syntax.sigquals);
                                              FStar_Syntax_Syntax.sigmeta =
                                                (se.FStar_Syntax_Syntax.sigmeta);
                                              FStar_Syntax_Syntax.sigattrs =
                                                (se.FStar_Syntax_Syntax.sigattrs);
                                              FStar_Syntax_Syntax.sigopens_and_abbrevs
                                                =
                                                (se.FStar_Syntax_Syntax.sigopens_and_abbrevs);
                                              FStar_Syntax_Syntax.sigopts =
                                                (se.FStar_Syntax_Syntax.sigopts)
                                            }))))))))
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
          { FStar_Syntax_Syntax.lid = tc; FStar_Syntax_Syntax.us = uvs;
            FStar_Syntax_Syntax.params = tps;
            FStar_Syntax_Syntax.num_uniform_params = n_uniform;
            FStar_Syntax_Syntax.t = k; FStar_Syntax_Syntax.mutuals = mutuals;
            FStar_Syntax_Syntax.ds = data;
            FStar_Syntax_Syntax.injective_type_params = uu___;_}
          ->
          let env0 = env in
          let uu___1 = FStar_Syntax_Subst.univ_var_opening uvs in
          (match uu___1 with
           | (usubst, uvs1) ->
               let uu___2 =
                 let uu___3 = FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                 let uu___4 = FStar_Syntax_Subst.subst_binders usubst tps in
                 let uu___5 =
                   let uu___6 =
                     FStar_Syntax_Subst.shift_subst
                       (FStar_Compiler_List.length tps) usubst in
                   FStar_Syntax_Subst.subst uu___6 k in
                 (uu___3, uu___4, uu___5) in
               (match uu___2 with
                | (env1, tps1, k1) ->
                    let uu___3 = FStar_Syntax_Subst.open_term tps1 k1 in
                    (match uu___3 with
                     | (tps2, k2) ->
                         let uu___4 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2 in
                         (match uu___4 with
                          | (tps3, env_tps, guard_params, us) ->
                              let uu___5 =
                                let uu___6 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2 in
                                match uu___6 with
                                | (k3, uu___7, g) ->
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
                                    let uu___8 =
                                      FStar_Syntax_Util.arrow_formals k4 in
                                    let uu___9 =
                                      let uu___10 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu___10 in
                                    (uu___8, uu___9) in
                              (match uu___5 with
                               | ((indices, t), guard) ->
                                   let k3 =
                                     let uu___6 =
                                       FStar_Syntax_Syntax.mk_Total t in
                                     FStar_Syntax_Util.arrow indices uu___6 in
                                   let uu___6 = FStar_Syntax_Util.type_u () in
                                   (match uu___6 with
                                    | (t_type, u) ->
                                        let valid_type =
                                          (((FStar_Syntax_Util.is_eqtype_no_unrefine
                                               t)
                                              &&
                                              (Prims.op_Negation
                                                 (FStar_Compiler_List.contains
                                                    FStar_Syntax_Syntax.Noeq
                                                    s.FStar_Syntax_Syntax.sigquals)))
                                             &&
                                             (Prims.op_Negation
                                                (FStar_Compiler_List.contains
                                                   FStar_Syntax_Syntax.Unopteq
                                                   s.FStar_Syntax_Syntax.sigquals)))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type) in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu___8 =
                                              let uu___9 =
                                                let uu___10 =
                                                  let uu___11 =
                                                    FStar_Class_Show.show
                                                      FStar_Syntax_Print.showable_term
                                                      t in
                                                  let uu___12 =
                                                    FStar_Class_Show.show
                                                      FStar_Ident.showable_lident
                                                      tc in
                                                  FStar_Compiler_Util.format2
                                                    "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains noeq/unopteq qualifiers"
                                                    uu___11 uu___12 in
                                                FStar_Errors_Msg.text uu___10 in
                                              [uu___9] in
                                            FStar_Errors.raise_error
                                              FStar_Syntax_Syntax.has_range_sigelt
                                              s
                                              FStar_Errors_Codes.Error_InductiveAnnotNotAType
                                              ()
                                              (Obj.magic
                                                 FStar_Errors_Msg.is_error_message_list_doc)
                                              (Obj.magic uu___8))
                                         else ();
                                         (let usubst1 =
                                            FStar_Syntax_Subst.univ_var_closing
                                              uvs1 in
                                          let guard1 =
                                            FStar_TypeChecker_Util.close_guard_implicits
                                              env1 false tps3 guard in
                                          let t_tc =
                                            let uu___8 =
                                              let uu___9 =
                                                FStar_Syntax_Subst.subst_binders
                                                  usubst1 tps3 in
                                              let uu___10 =
                                                let uu___11 =
                                                  FStar_Syntax_Subst.shift_subst
                                                    (FStar_Compiler_List.length
                                                       tps3) usubst1 in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu___11 indices in
                                              FStar_Compiler_List.op_At
                                                uu___9 uu___10 in
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
                                                  uu___11 t in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu___10 in
                                            FStar_Syntax_Util.arrow uu___8
                                              uu___9 in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3 in
                                          let uu___8 =
                                            let uu___9 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4 in
                                            let uu___10 =
                                              let uu___11 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_Compiler_List.length
                                                     tps4) usubst1 in
                                              FStar_Syntax_Subst.subst
                                                uu___11 k4 in
                                            (uu___9, uu___10) in
                                          match uu___8 with
                                          | (tps5, k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Pervasives_Native.None in
                                              let uu___9 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs1 t_tc in
                                              (match uu___9 with
                                               | (uvs2, t_tc1) ->
                                                   let uu___10 =
                                                     FStar_TypeChecker_Env.push_let_binding
                                                       env0
                                                       (FStar_Pervasives.Inr
                                                          fv_tc)
                                                       (uvs2, t_tc1) in
                                                   (uu___10,
                                                     {
                                                       FStar_Syntax_Syntax.sigel
                                                         =
                                                         (FStar_Syntax_Syntax.Sig_inductive_typ
                                                            {
                                                              FStar_Syntax_Syntax.lid
                                                                = tc;
                                                              FStar_Syntax_Syntax.us
                                                                = uvs2;
                                                              FStar_Syntax_Syntax.params
                                                                = tps5;
                                                              FStar_Syntax_Syntax.num_uniform_params
                                                                = n_uniform;
                                                              FStar_Syntax_Syntax.t
                                                                = k5;
                                                              FStar_Syntax_Syntax.mutuals
                                                                = mutuals;
                                                              FStar_Syntax_Syntax.ds
                                                                = data;
                                                              FStar_Syntax_Syntax.injective_type_params
                                                                = false
                                                            });
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
                                                       FStar_Syntax_Syntax.sigopens_and_abbrevs
                                                         =
                                                         (s.FStar_Syntax_Syntax.sigopens_and_abbrevs);
                                                       FStar_Syntax_Syntax.sigopts
                                                         =
                                                         (s.FStar_Syntax_Syntax.sigopts)
                                                     }, u, guard1))))))))))
      | uu___ -> failwith "impossible"
let (mk_implicit : FStar_Syntax_Syntax.bqual -> FStar_Syntax_Syntax.bqual) =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta q) ->
        FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta q)
    | uu___1 ->
        FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit false)
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
            { FStar_Syntax_Syntax.lid1 = c; FStar_Syntax_Syntax.us1 = _uvs;
              FStar_Syntax_Syntax.t1 = t;
              FStar_Syntax_Syntax.ty_lid = tc_lid;
              FStar_Syntax_Syntax.num_ty_params = ntps;
              FStar_Syntax_Syntax.mutuals1 = mutual_tcs;
              FStar_Syntax_Syntax.injective_type_params1 = uu___;_}
            ->
            let uu___1 = FStar_Syntax_Subst.univ_var_opening _uvs in
            (match uu___1 with
             | (usubst, _uvs1) ->
                 let uu___2 =
                   let uu___3 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1 in
                   let uu___4 = FStar_Syntax_Subst.subst usubst t in
                   (uu___3, uu___4) in
                 (match uu___2 with
                  | (env1, t1) ->
                      let uu___3 =
                        let tps_u_opt =
                          FStar_Compiler_Util.find_map tcs
                            (fun uu___4 ->
                               match uu___4 with
                               | (se1, u_tc) ->
                                   let uu___5 =
                                     let uu___6 =
                                       let uu___7 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Compiler_Util.must uu___7 in
                                     FStar_Ident.lid_equals tc_lid uu___6 in
                                   if uu___5
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          { FStar_Syntax_Syntax.lid = uu___6;
                                            FStar_Syntax_Syntax.us = uu___7;
                                            FStar_Syntax_Syntax.params = tps;
                                            FStar_Syntax_Syntax.num_uniform_params
                                              = uu___8;
                                            FStar_Syntax_Syntax.t = uu___9;
                                            FStar_Syntax_Syntax.mutuals =
                                              uu___10;
                                            FStar_Syntax_Syntax.ds = uu___11;
                                            FStar_Syntax_Syntax.injective_type_params
                                              = uu___12;_}
                                          ->
                                          let tps1 =
                                            let uu___13 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst tps in
                                            FStar_Compiler_List.map
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
                                                 }) uu___13 in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1 in
                                          let uu___13 =
                                            let uu___14 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2 in
                                            (uu___14, tps2, u_tc) in
                                          FStar_Pervasives_Native.Some
                                            uu___13
                                      | uu___6 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None) in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None ->
                            let uu___4 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid in
                            if uu___4
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                FStar_Syntax_Syntax.has_range_sigelt se
                                FStar_Errors_Codes.Fatal_UnexpectedDataConstructor
                                ()
                                (Obj.magic
                                   FStar_Errors_Msg.is_error_message_string)
                                (Obj.magic "Unexpected data constructor") in
                      (match uu___3 with
                       | (env2, tps, u_tc) ->
                           let uu___4 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_Compiler_List.op_At
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1 in
                             let t3 = FStar_Syntax_Util.canon_arrow t2 in
                             let uu___5 =
                               let uu___6 = FStar_Syntax_Subst.compress t3 in
                               uu___6.FStar_Syntax_Syntax.n in
                             match uu___5 with
                             | FStar_Syntax_Syntax.Tm_arrow
                                 { FStar_Syntax_Syntax.bs1 = bs;
                                   FStar_Syntax_Syntax.comp = res;_}
                                 ->
                                 let uu___6 =
                                   FStar_Compiler_Util.first_N ntps bs in
                                 (match uu___6 with
                                  | (uu___7, bs') ->
                                      let t4 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             {
                                               FStar_Syntax_Syntax.bs1 = bs';
                                               FStar_Syntax_Syntax.comp = res
                                             }) t3.FStar_Syntax_Syntax.pos in
                                      let subst =
                                        FStar_Compiler_List.mapi
                                          (fun i ->
                                             fun uu___8 ->
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
                                                   FStar_Syntax_Syntax.DB
                                                     ((ntps -
                                                         (Prims.int_one + i)),
                                                       x)) tps in
                                      let uu___8 =
                                        let uu___9 =
                                          FStar_Syntax_Subst.subst subst t4 in
                                        FStar_Syntax_Util.arrow_formals_comp
                                          uu___9 in
                                      (match uu___8 with
                                       | (bs1, c1) ->
                                           let uu___9 =
                                             (FStar_Options.ml_ish ()) ||
                                               (FStar_Syntax_Util.is_total_comp
                                                  c1) in
                                           if uu___9
                                           then
                                             (bs1,
                                               (FStar_Syntax_Util.comp_result
                                                  c1))
                                           else
                                             FStar_Errors.raise_error
                                               FStar_Ident.hasrange_lident
                                               (FStar_Syntax_Util.comp_effect_name
                                                  c1)
                                               FStar_Errors_Codes.Fatal_UnexpectedConstructorType
                                               ()
                                               (Obj.magic
                                                  FStar_Errors_Msg.is_error_message_string)
                                               (Obj.magic
                                                  "Constructors cannot have effects")))
                             | uu___6 -> ([], t3) in
                           (match uu___4 with
                            | (arguments, result) ->
                                ((let uu___6 = FStar_Compiler_Debug.low () in
                                  if uu___6
                                  then
                                    let uu___7 =
                                      FStar_Class_Show.show
                                        FStar_Ident.showable_lident c in
                                    let uu___8 =
                                      FStar_Class_Show.show
                                        (FStar_Class_Show.show_list
                                           FStar_Syntax_Print.showable_binder)
                                        arguments in
                                    let uu___9 =
                                      FStar_Class_Show.show
                                        FStar_Syntax_Print.showable_term
                                        result in
                                    FStar_Compiler_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu___7 uu___8 uu___9
                                  else ());
                                 (let uu___6 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments in
                                  match uu___6 with
                                  | (arguments1, env', us) ->
                                      let type_u_tc =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_type u_tc)
                                          result.FStar_Syntax_Syntax.pos in
                                      let env'1 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          env' type_u_tc in
                                      let uu___7 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result in
                                      (match uu___7 with
                                       | (result1, res_lcomp) ->
                                           let uu___8 =
                                             FStar_Syntax_Util.head_and_args_full
                                               result1 in
                                           (match uu___8 with
                                            | (head, args) ->
                                                let g_uvs =
                                                  let uu___9 =
                                                    let uu___10 =
                                                      FStar_Syntax_Subst.compress
                                                        head in
                                                    uu___10.FStar_Syntax_Syntax.n in
                                                  match uu___9 with
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                      ({
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           FStar_Syntax_Syntax.Tm_fvar
                                                           fv;
                                                         FStar_Syntax_Syntax.pos
                                                           = uu___10;
                                                         FStar_Syntax_Syntax.vars
                                                           = uu___11;
                                                         FStar_Syntax_Syntax.hash_code
                                                           = uu___12;_},
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
                                                                 let uu___13
                                                                   =
                                                                   let uu___14
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Compiler_Range_Type.dummyRange in
                                                                   let uu___15
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Compiler_Range_Type.dummyRange in
                                                                   FStar_TypeChecker_Rel.teq
                                                                    env'1
                                                                    uu___14
                                                                    uu___15 in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g uu___13)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          tuvs _uvs1
                                                      else
                                                        FStar_Errors.raise_error
                                                          FStar_Syntax_Syntax.has_range_sigelt
                                                          se
                                                          FStar_Errors_Codes.Fatal_UnexpectedConstructorType
                                                          ()
                                                          (Obj.magic
                                                             FStar_Errors_Msg.is_error_message_string)
                                                          (Obj.magic
                                                             "Length of annotated universes does not match inferred universes")
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv when
                                                      FStar_Syntax_Syntax.fv_eq_lid
                                                        fv tc_lid
                                                      ->
                                                      FStar_TypeChecker_Env.trivial_guard
                                                  | uu___10 ->
                                                      let uu___11 =
                                                        let uu___12 =
                                                          FStar_Class_Show.show
                                                            FStar_Ident.showable_lident
                                                            tc_lid in
                                                        let uu___13 =
                                                          FStar_Class_Show.show
                                                            FStar_Syntax_Print.showable_term
                                                            head in
                                                        FStar_Compiler_Util.format2
                                                          "Expected a constructor of type %s; got %s"
                                                          uu___12 uu___13 in
                                                      FStar_Errors.raise_error
                                                        FStar_Syntax_Syntax.has_range_sigelt
                                                        se
                                                        FStar_Errors_Codes.Fatal_UnexpectedConstructorType
                                                        ()
                                                        (Obj.magic
                                                           FStar_Errors_Msg.is_error_message_string)
                                                        (Obj.magic uu___11) in
                                                let g =
                                                  FStar_Compiler_List.fold_left2
                                                    (fun g1 ->
                                                       fun uu___9 ->
                                                         fun u_x ->
                                                           match uu___9 with
                                                           | {
                                                               FStar_Syntax_Syntax.binder_bv
                                                                 = x;
                                                               FStar_Syntax_Syntax.binder_qual
                                                                 = uu___10;
                                                               FStar_Syntax_Syntax.binder_positivity
                                                                 = uu___11;
                                                               FStar_Syntax_Syntax.binder_attrs
                                                                 = uu___12;_}
                                                               ->
                                                               let uu___13 =
                                                                 FStar_TypeChecker_Rel.universe_inequality
                                                                   u_x u_tc in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g1 uu___13)
                                                    g_uvs arguments1 us in
                                                (FStar_Errors.stop_if_err ();
                                                 (let p_args =
                                                    let uu___10 =
                                                      FStar_Compiler_Util.first_N
                                                        (FStar_Compiler_List.length
                                                           tps) args in
                                                    FStar_Pervasives_Native.fst
                                                      uu___10 in
                                                  FStar_Compiler_List.iter2
                                                    (fun uu___11 ->
                                                       fun uu___12 ->
                                                         match (uu___11,
                                                                 uu___12)
                                                         with
                                                         | ({
                                                              FStar_Syntax_Syntax.binder_bv
                                                                = bv;
                                                              FStar_Syntax_Syntax.binder_qual
                                                                = uu___13;
                                                              FStar_Syntax_Syntax.binder_positivity
                                                                = uu___14;
                                                              FStar_Syntax_Syntax.binder_attrs
                                                                = uu___15;_},
                                                            (t2, uu___16)) ->
                                                             let uu___17 =
                                                               let uu___18 =
                                                                 FStar_Syntax_Subst.compress
                                                                   t2 in
                                                               uu___18.FStar_Syntax_Syntax.n in
                                                             (match uu___17
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_name
                                                                  bv' when
                                                                  FStar_Syntax_Syntax.bv_eq
                                                                    bv bv'
                                                                  -> ()
                                                              | uu___18 ->
                                                                  let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStar_Class_Show.show
                                                                    FStar_Syntax_Print.showable_bv
                                                                    bv in
                                                                    let uu___21
                                                                    =
                                                                    FStar_Class_Show.show
                                                                    FStar_Syntax_Print.showable_term
                                                                    t2 in
                                                                    FStar_Compiler_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu___20
                                                                    uu___21 in
                                                                  FStar_Errors.raise_error
                                                                    (
                                                                    FStar_Syntax_Syntax.has_range_syntax
                                                                    ()) t2
                                                                    FStar_Errors_Codes.Error_BadInductiveParam
                                                                    ()
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Errors_Msg.is_error_message_string)
                                                                    (
                                                                    Obj.magic
                                                                    uu___19)))
                                                    tps p_args;
                                                  (let ty =
                                                     let uu___11 =
                                                       unfold_whnf env2
                                                         res_lcomp.FStar_TypeChecker_Common.res_typ in
                                                     FStar_Syntax_Util.unrefine
                                                       uu___11 in
                                                   (let uu___12 =
                                                      let uu___13 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu___13.FStar_Syntax_Syntax.n in
                                                    match uu___12 with
                                                    | FStar_Syntax_Syntax.Tm_type
                                                        uu___13 -> ()
                                                    | uu___13 ->
                                                        let uu___14 =
                                                          let uu___15 =
                                                            FStar_Class_Show.show
                                                              FStar_Syntax_Print.showable_term
                                                              result1 in
                                                          let uu___16 =
                                                            FStar_Class_Show.show
                                                              FStar_Syntax_Print.showable_term
                                                              ty in
                                                          FStar_Compiler_Util.format2
                                                            "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                            uu___15 uu___16 in
                                                        FStar_Errors.raise_error
                                                          FStar_Syntax_Syntax.has_range_sigelt
                                                          se
                                                          FStar_Errors_Codes.Fatal_WrongResultTypeAfterConstrutor
                                                          ()
                                                          (Obj.magic
                                                             FStar_Errors_Msg.is_error_message_string)
                                                          (Obj.magic uu___14));
                                                   (let t2 =
                                                      let uu___12 =
                                                        let uu___13 =
                                                          FStar_Compiler_List.map
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
                                                               }) tps in
                                                        FStar_Compiler_List.op_At
                                                          uu___13 arguments1 in
                                                      let uu___13 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          result1 in
                                                      FStar_Syntax_Util.arrow
                                                        uu___12 uu___13 in
                                                    let t3 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        _uvs1 t2 in
                                                    ({
                                                       FStar_Syntax_Syntax.sigel
                                                         =
                                                         (FStar_Syntax_Syntax.Sig_datacon
                                                            {
                                                              FStar_Syntax_Syntax.lid1
                                                                = c;
                                                              FStar_Syntax_Syntax.us1
                                                                = _uvs1;
                                                              FStar_Syntax_Syntax.t1
                                                                = t3;
                                                              FStar_Syntax_Syntax.ty_lid
                                                                = tc_lid;
                                                              FStar_Syntax_Syntax.num_ty_params
                                                                = ntps;
                                                              FStar_Syntax_Syntax.mutuals1
                                                                = mutual_tcs;
                                                              FStar_Syntax_Syntax.injective_type_params1
                                                                = false
                                                            });
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
                                                       FStar_Syntax_Syntax.sigopens_and_abbrevs
                                                         =
                                                         (se.FStar_Syntax_Syntax.sigopens_and_abbrevs);
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
          FStar_Compiler_List.map
            (fun uu___ ->
               match uu___ with
               | (se, uu___1) ->
                   (match se.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        { FStar_Syntax_Syntax.lid = uu___2;
                          FStar_Syntax_Syntax.us = uu___3;
                          FStar_Syntax_Syntax.params = tps;
                          FStar_Syntax_Syntax.num_uniform_params = uu___4;
                          FStar_Syntax_Syntax.t = k;
                          FStar_Syntax_Syntax.mutuals = uu___5;
                          FStar_Syntax_Syntax.ds = uu___6;
                          FStar_Syntax_Syntax.injective_type_params = uu___7;_}
                        ->
                        let uu___8 =
                          let uu___9 = FStar_Syntax_Syntax.mk_Total k in
                          FStar_Syntax_Util.arrow tps uu___9 in
                        FStar_Syntax_Syntax.null_binder uu___8
                    | uu___2 -> failwith "Impossible")) tcs in
        let binders' =
          FStar_Compiler_List.map
            (fun se ->
               match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_datacon
                   { FStar_Syntax_Syntax.lid1 = uu___;
                     FStar_Syntax_Syntax.us1 = uu___1;
                     FStar_Syntax_Syntax.t1 = t;
                     FStar_Syntax_Syntax.ty_lid = uu___2;
                     FStar_Syntax_Syntax.num_ty_params = uu___3;
                     FStar_Syntax_Syntax.mutuals1 = uu___4;
                     FStar_Syntax_Syntax.injective_type_params1 = uu___5;_}
                   -> FStar_Syntax_Syntax.null_binder t
               | uu___ -> failwith "Impossible") datas in
        let t =
          let uu___ = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
          FStar_Syntax_Util.arrow
            (FStar_Compiler_List.op_At binders binders') uu___ in
        (let uu___1 = FStar_Compiler_Effect.op_Bang dbg_GenUniverses in
         if uu___1
         then
           let uu___2 = FStar_TypeChecker_Normalize.term_to_string env t in
           FStar_Compiler_Util.print1
             "@@@@@@Trying to generalize universes in %s\n" uu___2
         else ());
        (let uu___1 = FStar_TypeChecker_Generalize.generalize_universes env t in
         match uu___1 with
         | (uvs, t1) ->
             ((let uu___3 = FStar_Compiler_Effect.op_Bang dbg_GenUniverses in
               if uu___3
               then
                 let uu___4 =
                   let uu___5 =
                     FStar_Compiler_List.map
                       (fun u -> FStar_Ident.string_of_id u) uvs in
                   FStar_Compiler_String.concat ", " uu___5 in
                 let uu___5 =
                   FStar_Class_Show.show FStar_Syntax_Print.showable_term t1 in
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
                                               {
                                                 FStar_Syntax_Syntax.lid = tc;
                                                 FStar_Syntax_Syntax.us =
                                                   uu___13;
                                                 FStar_Syntax_Syntax.params =
                                                   tps;
                                                 FStar_Syntax_Syntax.num_uniform_params
                                                   = num_uniform;
                                                 FStar_Syntax_Syntax.t =
                                                   uu___14;
                                                 FStar_Syntax_Syntax.mutuals
                                                   = mutuals;
                                                 FStar_Syntax_Syntax.ds =
                                                   datas1;
                                                 FStar_Syntax_Syntax.injective_type_params
                                                   = uu___15;_}
                                               ->
                                               let ty =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs1
                                                   x.FStar_Syntax_Syntax.sort in
                                               let uu___16 =
                                                 let uu___17 =
                                                   let uu___18 =
                                                     FStar_Syntax_Subst.compress
                                                       ty in
                                                   uu___18.FStar_Syntax_Syntax.n in
                                                 match uu___17 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     {
                                                       FStar_Syntax_Syntax.bs1
                                                         = binders1;
                                                       FStar_Syntax_Syntax.comp
                                                         = c;_}
                                                     ->
                                                     let uu___18 =
                                                       FStar_Compiler_Util.first_N
                                                         (FStar_Compiler_List.length
                                                            tps) binders1 in
                                                     (match uu___18 with
                                                      | (tps1, rest) ->
                                                          let t3 =
                                                            match rest with
                                                            | [] ->
                                                                FStar_Syntax_Util.comp_result
                                                                  c
                                                            | uu___19 ->
                                                                FStar_Syntax_Syntax.mk
                                                                  (FStar_Syntax_Syntax.Tm_arrow
                                                                    {
                                                                    FStar_Syntax_Syntax.bs1
                                                                    = rest;
                                                                    FStar_Syntax_Syntax.comp
                                                                    = c
                                                                    })
                                                                  (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                          (tps1, t3))
                                                 | uu___18 -> ([], ty) in
                                               (match uu___16 with
                                                | (tps1, t3) ->
                                                    {
                                                      FStar_Syntax_Syntax.sigel
                                                        =
                                                        (FStar_Syntax_Syntax.Sig_inductive_typ
                                                           {
                                                             FStar_Syntax_Syntax.lid
                                                               = tc;
                                                             FStar_Syntax_Syntax.us
                                                               = uvs1;
                                                             FStar_Syntax_Syntax.params
                                                               = tps1;
                                                             FStar_Syntax_Syntax.num_uniform_params
                                                               = num_uniform;
                                                             FStar_Syntax_Syntax.t
                                                               = t3;
                                                             FStar_Syntax_Syntax.mutuals
                                                               = mutuals;
                                                             FStar_Syntax_Syntax.ds
                                                               = datas1;
                                                             FStar_Syntax_Syntax.injective_type_params
                                                               = false
                                                           });
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
                                                      FStar_Syntax_Syntax.sigopens_and_abbrevs
                                                        =
                                                        (se.FStar_Syntax_Syntax.sigopens_and_abbrevs);
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
                                     FStar_Compiler_List.map
                                       (fun uu___8 ->
                                          FStar_Syntax_Syntax.U_name uu___8)
                                       uvs1 in
                                   let tc_insts =
                                     FStar_Compiler_List.map
                                       (fun uu___8 ->
                                          match uu___8 with
                                          | {
                                              FStar_Syntax_Syntax.sigel =
                                                FStar_Syntax_Syntax.Sig_inductive_typ
                                                {
                                                  FStar_Syntax_Syntax.lid =
                                                    tc;
                                                  FStar_Syntax_Syntax.us =
                                                    uu___9;
                                                  FStar_Syntax_Syntax.params
                                                    = uu___10;
                                                  FStar_Syntax_Syntax.num_uniform_params
                                                    = uu___11;
                                                  FStar_Syntax_Syntax.t =
                                                    uu___12;
                                                  FStar_Syntax_Syntax.mutuals
                                                    = uu___13;
                                                  FStar_Syntax_Syntax.ds =
                                                    uu___14;
                                                  FStar_Syntax_Syntax.injective_type_params
                                                    = uu___15;_};
                                              FStar_Syntax_Syntax.sigrng =
                                                uu___16;
                                              FStar_Syntax_Syntax.sigquals =
                                                uu___17;
                                              FStar_Syntax_Syntax.sigmeta =
                                                uu___18;
                                              FStar_Syntax_Syntax.sigattrs =
                                                uu___19;
                                              FStar_Syntax_Syntax.sigopens_and_abbrevs
                                                = uu___20;
                                              FStar_Syntax_Syntax.sigopts =
                                                uu___21;_}
                                              -> (tc, uvs_universes)
                                          | uu___9 -> failwith "Impossible")
                                       tcs1 in
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
                                                   {
                                                     FStar_Syntax_Syntax.lid1
                                                       = l;
                                                     FStar_Syntax_Syntax.us1
                                                       = uu___12;
                                                     FStar_Syntax_Syntax.t1 =
                                                       uu___13;
                                                     FStar_Syntax_Syntax.ty_lid
                                                       = tc;
                                                     FStar_Syntax_Syntax.num_ty_params
                                                       = ntps;
                                                     FStar_Syntax_Syntax.mutuals1
                                                       = mutuals;
                                                     FStar_Syntax_Syntax.injective_type_params1
                                                       = uu___14;_}
                                                   ->
                                                   let ty =
                                                     let uu___15 =
                                                       FStar_Syntax_InstFV.instantiate
                                                         tc_insts
                                                         t3.FStar_Syntax_Syntax.sort in
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs1 uu___15 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          {
                                                            FStar_Syntax_Syntax.lid1
                                                              = l;
                                                            FStar_Syntax_Syntax.us1
                                                              = uvs1;
                                                            FStar_Syntax_Syntax.t1
                                                              = ty;
                                                            FStar_Syntax_Syntax.ty_lid
                                                              = tc;
                                                            FStar_Syntax_Syntax.num_ty_params
                                                              = ntps;
                                                            FStar_Syntax_Syntax.mutuals1
                                                              = mutuals;
                                                            FStar_Syntax_Syntax.injective_type_params1
                                                              = false
                                                          });
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
                                                     FStar_Syntax_Syntax.sigopens_and_abbrevs
                                                       =
                                                       (d.FStar_Syntax_Syntax.sigopens_and_abbrevs);
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
        { FStar_Syntax_Syntax.lid1 = uu___; FStar_Syntax_Syntax.us1 = uu___1;
          FStar_Syntax_Syntax.t1 = t; FStar_Syntax_Syntax.ty_lid = uu___2;
          FStar_Syntax_Syntax.num_ty_params = uu___3;
          FStar_Syntax_Syntax.mutuals1 = uu___4;
          FStar_Syntax_Syntax.injective_type_params1 = uu___5;_}
        -> t
    | uu___ -> failwith "Impossible!"
let (haseq_suffix : Prims.string) = "__uu___haseq"
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid ->
    let str = FStar_Ident.string_of_lid lid in
    let len = FStar_Compiler_String.length str in
    let haseq_suffix_len = FStar_Compiler_String.length haseq_suffix in
    (len > haseq_suffix_len) &&
      (let uu___ =
         let uu___1 =
           FStar_Compiler_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len in
         FStar_Compiler_String.compare uu___1 haseq_suffix in
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
            Prims.strcat uu___5 haseq_suffix in
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
                { FStar_Syntax_Syntax.lid = lid;
                  FStar_Syntax_Syntax.us = uu___1;
                  FStar_Syntax_Syntax.params = bs;
                  FStar_Syntax_Syntax.num_uniform_params = uu___2;
                  FStar_Syntax_Syntax.t = t;
                  FStar_Syntax_Syntax.mutuals = uu___3;
                  FStar_Syntax_Syntax.ds = uu___4;
                  FStar_Syntax_Syntax.injective_type_params = uu___5;_}
                -> (lid, bs, t)
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
                     | FStar_Syntax_Syntax.Tm_arrow
                         { FStar_Syntax_Syntax.bs1 = ibs1;
                           FStar_Syntax_Syntax.comp = uu___3;_}
                         -> ibs1
                     | uu___3 -> [] in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                   let ind =
                     let uu___2 =
                       FStar_Syntax_Syntax.fvar lid
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
                         {
                           FStar_Syntax_Syntax.tm2 = fml;
                           FStar_Syntax_Syntax.meta = uu___4
                         } in
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
          | FStar_Syntax_Syntax.Tm_arrow
              { FStar_Syntax_Syntax.bs1 = dbs;
                FStar_Syntax_Syntax.comp = uu___1;_}
              ->
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
                           let uu___3 =
                             let uu___4 =
                               FStar_Errors_Msg.text
                                 "Failed to prove that the type" in
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   FStar_Class_PP.pp
                                     FStar_Ident.pretty_lident ty_lid in
                                 FStar_Pprint.squotes uu___7 in
                               let uu___7 =
                                 FStar_Errors_Msg.text
                                   "supports decidable equality because of this argument." in
                               FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                             FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                           let uu___4 =
                             let uu___5 =
                               FStar_Errors_Msg.text
                                 "Add either the 'noeq' or 'unopteq' qualifier" in
                             [uu___5] in
                           uu___3 :: uu___4 in
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
                  { FStar_Syntax_Syntax.lid = lid1;
                    FStar_Syntax_Syntax.us = uu___;
                    FStar_Syntax_Syntax.params = uu___1;
                    FStar_Syntax_Syntax.num_uniform_params = uu___2;
                    FStar_Syntax_Syntax.t = uu___3;
                    FStar_Syntax_Syntax.mutuals = uu___4;
                    FStar_Syntax_Syntax.ds = uu___5;
                    FStar_Syntax_Syntax.injective_type_params = uu___6;_}
                  -> lid1
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
                                     { FStar_Syntax_Syntax.lid1 = uu___6;
                                       FStar_Syntax_Syntax.us1 = uu___7;
                                       FStar_Syntax_Syntax.t1 = uu___8;
                                       FStar_Syntax_Syntax.ty_lid = t_lid;
                                       FStar_Syntax_Syntax.num_ty_params =
                                         uu___9;
                                       FStar_Syntax_Syntax.mutuals1 = uu___10;
                                       FStar_Syntax_Syntax.injective_type_params1
                                         = uu___11;_}
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
                { FStar_Syntax_Syntax.lid = uu___1;
                  FStar_Syntax_Syntax.us = us;
                  FStar_Syntax_Syntax.params = uu___2;
                  FStar_Syntax_Syntax.num_uniform_params = uu___3;
                  FStar_Syntax_Syntax.t = t;
                  FStar_Syntax_Syntax.mutuals = uu___4;
                  FStar_Syntax_Syntax.ds = uu___5;
                  FStar_Syntax_Syntax.injective_type_params = uu___6;_}
                -> (us, t)
            | uu___1 -> failwith "Impossible!" in
          match uu___ with
          | (us, t) ->
              let uu___1 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu___1 with
               | (usubst, us1) ->
                   let env = FStar_TypeChecker_Env.push env0 "haseq" in
                   let env1 =
                     FStar_TypeChecker_Env.push_sigelt_force env sig_bndle in
                   ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env1 sig_bndle;
                    (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 us1 in
                     let uu___3 =
                       FStar_Compiler_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env2, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs in
                     match uu___3 with
                     | (axioms, env3, guard, cond) ->
                         let phi =
                           let uu___4 = FStar_Syntax_Util.arrow_formals t in
                           match uu___4 with
                           | (uu___5, t1) ->
                               let uu___6 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1 in
                               if uu___6
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond in
                         let uu___4 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env3 phi in
                         (match uu___4 with
                          | (phi1, uu___5) ->
                              ((let uu___7 =
                                  FStar_TypeChecker_Env.should_verify env3 in
                                if uu___7
                                then
                                  let uu___8 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1) in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env3 uu___8
                                else ());
                               (let ses =
                                  FStar_Compiler_List.fold_left
                                    (fun l ->
                                       fun uu___7 ->
                                         match uu___7 with
                                         | (lid, fml) ->
                                             let fml1 =
                                               FStar_Syntax_Subst.close_univ_vars
                                                 us1 fml in
                                             FStar_Compiler_List.op_At l
                                               [{
                                                  FStar_Syntax_Syntax.sigel =
                                                    (FStar_Syntax_Syntax.Sig_assume
                                                       {
                                                         FStar_Syntax_Syntax.lid3
                                                           = lid;
                                                         FStar_Syntax_Syntax.us3
                                                           = us1;
                                                         FStar_Syntax_Syntax.phi1
                                                           = fml1
                                                       });
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
                                                  FStar_Syntax_Syntax.sigopens_and_abbrevs
                                                    = [];
                                                  FStar_Syntax_Syntax.sigopts
                                                    =
                                                    FStar_Pervasives_Native.None
                                                }]) [] axioms in
                                (let uu___8 =
                                   FStar_TypeChecker_Env.pop env3 "haseq" in
                                 ());
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
                | FStar_Syntax_Syntax.Tm_refine
                    { FStar_Syntax_Syntax.b = bv;
                      FStar_Syntax_Syntax.phi = uu___1;_}
                    -> is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app
                    { FStar_Syntax_Syntax.hd = t';
                      FStar_Syntax_Syntax.args = args;_}
                    ->
                    let uu___1 = is_mutual t' in
                    if uu___1
                    then true
                    else
                      (let uu___3 =
                         FStar_Compiler_List.map FStar_Pervasives_Native.fst
                           args in
                       exists_mutual uu___3)
                | FStar_Syntax_Syntax.Tm_meta
                    { FStar_Syntax_Syntax.tm2 = t';
                      FStar_Syntax_Syntax.meta = uu___1;_}
                    -> is_mutual t'
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
              | FStar_Syntax_Syntax.Tm_arrow
                  { FStar_Syntax_Syntax.bs1 = dbs;
                    FStar_Syntax_Syntax.comp = uu___1;_}
                  ->
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
                    { FStar_Syntax_Syntax.lid = lid;
                      FStar_Syntax_Syntax.us = uu___1;
                      FStar_Syntax_Syntax.params = bs;
                      FStar_Syntax_Syntax.num_uniform_params = uu___2;
                      FStar_Syntax_Syntax.t = t;
                      FStar_Syntax_Syntax.mutuals = uu___3;
                      FStar_Syntax_Syntax.ds = d_lids;
                      FStar_Syntax_Syntax.injective_type_params = uu___4;_}
                    -> (lid, bs, t, d_lids)
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
                         | FStar_Syntax_Syntax.Tm_arrow
                             { FStar_Syntax_Syntax.bs1 = ibs1;
                               FStar_Syntax_Syntax.comp = uu___3;_}
                             -> ibs1
                         | uu___3 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu___2 =
                           FStar_Syntax_Syntax.fvar lid
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
                                  { FStar_Syntax_Syntax.lid1 = uu___2;
                                    FStar_Syntax_Syntax.us1 = uu___3;
                                    FStar_Syntax_Syntax.t1 = uu___4;
                                    FStar_Syntax_Syntax.ty_lid = t_lid;
                                    FStar_Syntax_Syntax.num_ty_params =
                                      uu___5;
                                    FStar_Syntax_Syntax.mutuals1 = uu___6;
                                    FStar_Syntax_Syntax.injective_type_params1
                                      = uu___7;_}
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
                             {
                               FStar_Syntax_Syntax.tm2 = fml;
                               FStar_Syntax_Syntax.meta = uu___4
                             } in
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
                     { FStar_Syntax_Syntax.lid = lid;
                       FStar_Syntax_Syntax.us = uu___;
                       FStar_Syntax_Syntax.params = uu___1;
                       FStar_Syntax_Syntax.num_uniform_params = uu___2;
                       FStar_Syntax_Syntax.t = uu___3;
                       FStar_Syntax_Syntax.mutuals = uu___4;
                       FStar_Syntax_Syntax.ds = uu___5;
                       FStar_Syntax_Syntax.injective_type_params = uu___6;_}
                     -> lid
                 | uu___ -> failwith "Impossible!") tcs in
          let uu___ =
            let ty = FStar_Compiler_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                { FStar_Syntax_Syntax.lid = lid; FStar_Syntax_Syntax.us = us;
                  FStar_Syntax_Syntax.params = uu___1;
                  FStar_Syntax_Syntax.num_uniform_params = uu___2;
                  FStar_Syntax_Syntax.t = uu___3;
                  FStar_Syntax_Syntax.mutuals = uu___4;
                  FStar_Syntax_Syntax.ds = uu___5;
                  FStar_Syntax_Syntax.injective_type_params = uu___6;_}
                -> (lid, us)
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
                         {
                           FStar_Syntax_Syntax.lid3 = uu___4;
                           FStar_Syntax_Syntax.us3 = us1;
                           FStar_Syntax_Syntax.phi1 = fml
                         } in
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
                       FStar_Syntax_Syntax.sigopens_and_abbrevs = [];
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
            FStar_Compiler_List.partition
              (fun uu___1 ->
                 match uu___1 with
                 | {
                     FStar_Syntax_Syntax.sigel =
                       FStar_Syntax_Syntax.Sig_inductive_typ uu___2;
                     FStar_Syntax_Syntax.sigrng = uu___3;
                     FStar_Syntax_Syntax.sigquals = uu___4;
                     FStar_Syntax_Syntax.sigmeta = uu___5;
                     FStar_Syntax_Syntax.sigattrs = uu___6;
                     FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___7;
                     FStar_Syntax_Syntax.sigopts = uu___8;_} -> true
                 | uu___2 -> false) ses in
          match uu___ with
          | (tys, datas) ->
              ((let uu___2 =
                  FStar_Compiler_Util.for_some
                    (fun uu___3 ->
                       match uu___3 with
                       | {
                           FStar_Syntax_Syntax.sigel =
                             FStar_Syntax_Syntax.Sig_datacon uu___4;
                           FStar_Syntax_Syntax.sigrng = uu___5;
                           FStar_Syntax_Syntax.sigquals = uu___6;
                           FStar_Syntax_Syntax.sigmeta = uu___7;
                           FStar_Syntax_Syntax.sigattrs = uu___8;
                           FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___9;
                           FStar_Syntax_Syntax.sigopts = uu___10;_} -> false
                       | uu___4 -> true) datas in
                if uu___2
                then
                  FStar_Errors.raise_error FStar_TypeChecker_Env.hasRange_env
                    env
                    FStar_Errors_Codes.Fatal_NonInductiveInMutuallyDefinedType
                    () (Obj.magic FStar_Errors_Msg.is_error_message_string)
                    (Obj.magic
                       "Mutually defined type contains a non-inductive element")
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
                         { FStar_Syntax_Syntax.lid = uu___4;
                           FStar_Syntax_Syntax.us = uvs;
                           FStar_Syntax_Syntax.params = uu___5;
                           FStar_Syntax_Syntax.num_uniform_params = uu___6;
                           FStar_Syntax_Syntax.t = uu___7;
                           FStar_Syntax_Syntax.mutuals = uu___8;
                           FStar_Syntax_Syntax.ds = uu___9;
                           FStar_Syntax_Syntax.injective_type_params =
                             uu___10;_}
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
                                  ((let uu___6 = FStar_Compiler_Debug.low () in
                                    if uu___6
                                    then
                                      let uu___7 =
                                        FStar_Class_Show.show
                                          FStar_Syntax_Print.showable_sigelt
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
                    let g1 = FStar_TypeChecker_Rel.resolve_implicits env1 g in
                    let uu___3 =
                      FStar_Compiler_List.fold_right
                        (fun se ->
                           fun uu___4 ->
                             match uu___4 with
                             | (datas1, g2) ->
                                 let uu___5 =
                                   let uu___6 = tc_data env1 tcs in uu___6 se in
                                 (match uu___5 with
                                  | (data, g') ->
                                      let uu___6 =
                                        FStar_TypeChecker_Env.conj_guard g2
                                          g' in
                                      ((data :: datas1), uu___6))) datas
                        ([], g1) in
                    (match uu___3 with
                     | (datas1, g2) ->
                         let uu___4 =
                           let tc_universe_vars =
                             FStar_Compiler_List.map
                               FStar_Pervasives_Native.snd tcs in
                           let g3 =
                             let uu___5 =
                               let uu___6 =
                                 FStar_Class_Listlike.from_list
                                   (FStar_Compiler_CList.listlike_clist ())
                                   tc_universe_vars in
                               (uu___6,
                                 (FStar_Pervasives_Native.snd
                                    g2.FStar_TypeChecker_Common.univ_ineqs)) in
                             {
                               FStar_TypeChecker_Common.guard_f =
                                 (g2.FStar_TypeChecker_Common.guard_f);
                               FStar_TypeChecker_Common.deferred_to_tac =
                                 (g2.FStar_TypeChecker_Common.deferred_to_tac);
                               FStar_TypeChecker_Common.deferred =
                                 (g2.FStar_TypeChecker_Common.deferred);
                               FStar_TypeChecker_Common.univ_ineqs = uu___5;
                               FStar_TypeChecker_Common.implicits =
                                 (g2.FStar_TypeChecker_Common.implicits)
                             } in
                           (let uu___6 =
                              FStar_Compiler_Effect.op_Bang dbg_GenUniverses in
                            if uu___6
                            then
                              let uu___7 =
                                FStar_TypeChecker_Rel.guard_to_string env1 g3 in
                              FStar_Compiler_Util.print1
                                "@@@@@@Guard before (possible) generalization: %s\n"
                                uu___7
                            else ());
                           FStar_TypeChecker_Rel.force_trivial_guard env0 g3;
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
                                FStar_Compiler_List.map
                                  (fun se ->
                                     match se.FStar_Syntax_Syntax.sigel with
                                     | FStar_Syntax_Syntax.Sig_inductive_typ
                                         { FStar_Syntax_Syntax.lid = l;
                                           FStar_Syntax_Syntax.us = univs1;
                                           FStar_Syntax_Syntax.params =
                                             binders;
                                           FStar_Syntax_Syntax.num_uniform_params
                                             = num_uniform;
                                           FStar_Syntax_Syntax.t = typ;
                                           FStar_Syntax_Syntax.mutuals = ts;
                                           FStar_Syntax_Syntax.ds = ds;
                                           FStar_Syntax_Syntax.injective_type_params
                                             = uu___5;_}
                                         ->
                                         let fail expected inferred =
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
                                           FStar_Errors.raise_error
                                             FStar_Syntax_Syntax.has_range_sigelt
                                             se
                                             FStar_Errors_Codes.Fatal_UnexpectedInductivetype
                                             ()
                                             (Obj.magic
                                                FStar_Errors_Msg.is_error_message_string)
                                             (Obj.magic uu___6) in
                                         let copy_binder_attrs_from_val
                                           binders1 expected =
                                           let expected_attrs =
                                             let uu___6 =
                                               let uu___7 =
                                                 FStar_TypeChecker_Normalize.get_n_binders
                                                   env1
                                                   (FStar_Compiler_List.length
                                                      binders1) expected in
                                               FStar_Pervasives_Native.fst
                                                 uu___7 in
                                             FStar_Compiler_List.map
                                               (fun uu___7 ->
                                                  match uu___7 with
                                                  | {
                                                      FStar_Syntax_Syntax.binder_bv
                                                        = uu___8;
                                                      FStar_Syntax_Syntax.binder_qual
                                                        = uu___9;
                                                      FStar_Syntax_Syntax.binder_positivity
                                                        = pqual;
                                                      FStar_Syntax_Syntax.binder_attrs
                                                        = attrs;_}
                                                      -> (attrs, pqual))
                                               uu___6 in
                                           if
                                             (FStar_Compiler_List.length
                                                expected_attrs)
                                               <>
                                               (FStar_Compiler_List.length
                                                  binders1)
                                           then
                                             let uu___6 =
                                               let uu___7 =
                                                 FStar_Compiler_Util.string_of_int
                                                   (FStar_Compiler_List.length
                                                      binders1) in
                                               let uu___8 =
                                                 FStar_Class_Show.show
                                                   FStar_Syntax_Print.showable_term
                                                   expected in
                                               FStar_Compiler_Util.format2
                                                 "Could not get %s type parameters from val type %s"
                                                 uu___7 uu___8 in
                                             FStar_Errors.raise_error
                                               FStar_Syntax_Syntax.has_range_sigelt
                                               se
                                               FStar_Errors_Codes.Fatal_UnexpectedInductivetype
                                               ()
                                               (Obj.magic
                                                  FStar_Errors_Msg.is_error_message_string)
                                               (Obj.magic uu___6)
                                           else
                                             FStar_Compiler_List.map2
                                               (fun uu___7 ->
                                                  fun b ->
                                                    match uu___7 with
                                                    | (ex_attrs, pqual) ->
                                                        ((let uu___9 =
                                                            let uu___10 =
                                                              FStar_TypeChecker_Common.check_positivity_qual
                                                                true pqual
                                                                b.FStar_Syntax_Syntax.binder_positivity in
                                                            Prims.op_Negation
                                                              uu___10 in
                                                          if uu___9
                                                          then
                                                            FStar_Errors.raise_error
                                                              FStar_Syntax_Syntax.hasRange_binder
                                                              b
                                                              FStar_Errors_Codes.Fatal_UnexpectedInductivetype
                                                              ()
                                                              (Obj.magic
                                                                 FStar_Errors_Msg.is_error_message_string)
                                                              (Obj.magic
                                                                 "Incompatible positivity annotation")
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
                                                         })) expected_attrs
                                               binders1 in
                                         let inferred_typ_with_binders
                                           binders1 =
                                           let body =
                                             match binders1 with
                                             | [] -> typ
                                             | uu___6 ->
                                                 let uu___7 =
                                                   let uu___8 =
                                                     let uu___9 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         typ in
                                                     {
                                                       FStar_Syntax_Syntax.bs1
                                                         = binders1;
                                                       FStar_Syntax_Syntax.comp
                                                         = uu___9
                                                     } in
                                                   FStar_Syntax_Syntax.Tm_arrow
                                                     uu___8 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu___7
                                                   se.FStar_Syntax_Syntax.sigrng in
                                           (univs1, body) in
                                         let uu___6 =
                                           FStar_TypeChecker_Env.try_lookup_val_decl
                                             env0 l in
                                         (match uu___6 with
                                          | FStar_Pervasives_Native.None ->
                                              se
                                          | FStar_Pervasives_Native.Some
                                              (expected_typ, uu___7) ->
                                              if
                                                (FStar_Compiler_List.length
                                                   univs1)
                                                  =
                                                  (FStar_Compiler_List.length
                                                     (FStar_Pervasives_Native.fst
                                                        expected_typ))
                                              then
                                                let uu___8 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    univs1
                                                    (FStar_Pervasives_Native.snd
                                                       expected_typ) in
                                                (match uu___8 with
                                                 | (uu___9, expected) ->
                                                     let binders1 =
                                                       copy_binder_attrs_from_val
                                                         binders expected in
                                                     let inferred_typ =
                                                       inferred_typ_with_binders
                                                         binders1 in
                                                     let uu___10 =
                                                       FStar_Syntax_Subst.open_univ_vars
                                                         univs1
                                                         (FStar_Pervasives_Native.snd
                                                            inferred_typ) in
                                                     (match uu___10 with
                                                      | (uu___11, inferred)
                                                          ->
                                                          let uu___12 =
                                                            FStar_TypeChecker_Rel.teq_nosmt_force
                                                              env0 inferred
                                                              expected in
                                                          if uu___12
                                                          then
                                                            {
                                                              FStar_Syntax_Syntax.sigel
                                                                =
                                                                (FStar_Syntax_Syntax.Sig_inductive_typ
                                                                   {
                                                                    FStar_Syntax_Syntax.lid
                                                                    = l;
                                                                    FStar_Syntax_Syntax.us
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.params
                                                                    =
                                                                    binders1;
                                                                    FStar_Syntax_Syntax.num_uniform_params
                                                                    =
                                                                    num_uniform;
                                                                    FStar_Syntax_Syntax.t
                                                                    = typ;
                                                                    FStar_Syntax_Syntax.mutuals
                                                                    = ts;
                                                                    FStar_Syntax_Syntax.ds
                                                                    = ds;
                                                                    FStar_Syntax_Syntax.injective_type_params
                                                                    = false
                                                                   });
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
                                                              FStar_Syntax_Syntax.sigopens_and_abbrevs
                                                                =
                                                                (se.FStar_Syntax_Syntax.sigopens_and_abbrevs);
                                                              FStar_Syntax_Syntax.sigopts
                                                                =
                                                                (se.FStar_Syntax_Syntax.sigopts)
                                                            }
                                                          else
                                                            fail expected_typ
                                                              inferred_typ))
                                              else
                                                (let uu___9 =
                                                   inferred_typ_with_binders
                                                     binders in
                                                 fail expected_typ uu___9))
                                     | uu___5 -> se) tcs1 in
                              let tcs3 =
                                FStar_Compiler_List.map
                                  (check_sig_inductive_injectivity_on_params
                                     env0) tcs2 in
                              let is_injective l =
                                let uu___5 =
                                  FStar_Compiler_List.tryPick
                                    (fun se ->
                                       let uu___6 =
                                         se.FStar_Syntax_Syntax.sigel in
                                       match uu___6 with
                                       | FStar_Syntax_Syntax.Sig_inductive_typ
                                           { FStar_Syntax_Syntax.lid = lid;
                                             FStar_Syntax_Syntax.us = uu___7;
                                             FStar_Syntax_Syntax.params =
                                               uu___8;
                                             FStar_Syntax_Syntax.num_uniform_params
                                               = uu___9;
                                             FStar_Syntax_Syntax.t = uu___10;
                                             FStar_Syntax_Syntax.mutuals =
                                               uu___11;
                                             FStar_Syntax_Syntax.ds = uu___12;
                                             FStar_Syntax_Syntax.injective_type_params
                                               = injective_type_params;_}
                                           ->
                                           let uu___13 =
                                             FStar_Ident.lid_equals l lid in
                                           if uu___13
                                           then
                                             FStar_Pervasives_Native.Some
                                               injective_type_params
                                           else FStar_Pervasives_Native.None)
                                    tcs3 in
                                match uu___5 with
                                | FStar_Pervasives_Native.None -> false
                                | FStar_Pervasives_Native.Some i -> i in
                              let datas3 =
                                FStar_Compiler_List.map
                                  (fun se ->
                                     let uu___5 =
                                       se.FStar_Syntax_Syntax.sigel in
                                     match uu___5 with
                                     | FStar_Syntax_Syntax.Sig_datacon dd ->
                                         let uu___6 =
                                           let uu___7 =
                                             let uu___8 =
                                               is_injective
                                                 dd.FStar_Syntax_Syntax.ty_lid in
                                             {
                                               FStar_Syntax_Syntax.lid1 =
                                                 (dd.FStar_Syntax_Syntax.lid1);
                                               FStar_Syntax_Syntax.us1 =
                                                 (dd.FStar_Syntax_Syntax.us1);
                                               FStar_Syntax_Syntax.t1 =
                                                 (dd.FStar_Syntax_Syntax.t1);
                                               FStar_Syntax_Syntax.ty_lid =
                                                 (dd.FStar_Syntax_Syntax.ty_lid);
                                               FStar_Syntax_Syntax.num_ty_params
                                                 =
                                                 (dd.FStar_Syntax_Syntax.num_ty_params);
                                               FStar_Syntax_Syntax.mutuals1 =
                                                 (dd.FStar_Syntax_Syntax.mutuals1);
                                               FStar_Syntax_Syntax.injective_type_params1
                                                 = uu___8
                                             } in
                                           FStar_Syntax_Syntax.Sig_datacon
                                             uu___7 in
                                         {
                                           FStar_Syntax_Syntax.sigel = uu___6;
                                           FStar_Syntax_Syntax.sigrng =
                                             (se.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (se.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (se.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (se.FStar_Syntax_Syntax.sigattrs);
                                           FStar_Syntax_Syntax.sigopens_and_abbrevs
                                             =
                                             (se.FStar_Syntax_Syntax.sigopens_and_abbrevs);
                                           FStar_Syntax_Syntax.sigopts =
                                             (se.FStar_Syntax_Syntax.sigopts)
                                         }) datas2 in
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
                                       {
                                         FStar_Syntax_Syntax.ses =
                                           (FStar_Compiler_List.op_At tcs3
                                              datas3);
                                         FStar_Syntax_Syntax.lids = lids
                                       });
                                  FStar_Syntax_Syntax.sigrng = uu___5;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu___6;
                                  FStar_Syntax_Syntax.sigopens_and_abbrevs =
                                    [];
                                  FStar_Syntax_Syntax.sigopts =
                                    FStar_Pervasives_Native.None
                                } in
                              (sig_bndle, tcs3, datas3)))))
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
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.fv_to_tm uu___3 in
                                  (uu___2, inst_univs) in
                                FStar_Syntax_Syntax.Tm_uinst uu___1 in
                              FStar_Syntax_Syntax.mk uu___ p in
                            let args =
                              FStar_Compiler_List.map
                                FStar_Syntax_Util.arg_of_non_null_binder
                                (FStar_Compiler_List.op_At tps indices) in
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
                                   FStar_Syntax_Syntax.fvar_with_dd uu___1
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
                            FStar_Compiler_List.map
                              (fun b ->
                                 let uu___ =
                                   mk_implicit
                                     b.FStar_Syntax_Syntax.binder_qual in
                                 {
                                   FStar_Syntax_Syntax.binder_bv =
                                     (b.FStar_Syntax_Syntax.binder_bv);
                                   FStar_Syntax_Syntax.binder_qual = uu___;
                                   FStar_Syntax_Syntax.binder_positivity =
                                     (b.FStar_Syntax_Syntax.binder_positivity);
                                   FStar_Syntax_Syntax.binder_attrs =
                                     (b.FStar_Syntax_Syntax.binder_attrs)
                                 }) (FStar_Compiler_List.op_At tps indices) in
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
                                 FStar_Syntax_Subst.close_univ_vars uvs
                                   uu___1 in
                               let decl =
                                 let uu___1 =
                                   FStar_Ident.range_of_lid
                                     discriminator_name in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_declare_typ
                                        {
                                          FStar_Syntax_Syntax.lid2 =
                                            discriminator_name;
                                          FStar_Syntax_Syntax.us2 = uvs;
                                          FStar_Syntax_Syntax.t2 = t
                                        });
                                   FStar_Syntax_Syntax.sigrng = uu___1;
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = attrs;
                                   FStar_Syntax_Syntax.sigopens_and_abbrevs =
                                     [];
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 } in
                               (let uu___2 =
                                  FStar_Compiler_Effect.op_Bang dbg_LogTypes in
                                if uu___2
                                then
                                  let uu___3 =
                                    FStar_Class_Show.show
                                      FStar_Syntax_Print.showable_sigelt decl in
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
                                         FStar_Compiler_List.mapi
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
                                                           FStar_Syntax_Syntax.Pat_var
                                                             uu___10 in
                                                         pos uu___9 in
                                                       (uu___8, b)))
                                           all_params in
                                       let pat_true =
                                         let uu___4 =
                                           let uu___5 =
                                             let uu___6 =
                                               let uu___7 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   lid
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
                                             FStar_Syntax_Syntax.Pat_var
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
                                           {
                                             FStar_Syntax_Syntax.scrutinee =
                                               arg_exp;
                                             FStar_Syntax_Syntax.ret_opt =
                                               FStar_Pervasives_Native.None;
                                             FStar_Syntax_Syntax.brs = uu___6;
                                             FStar_Syntax_Syntax.rc_opt1 =
                                               FStar_Pervasives_Native.None
                                           } in
                                         FStar_Syntax_Syntax.Tm_match uu___5 in
                                       FStar_Syntax_Syntax.mk uu___4 p) in
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
                                        FStar_Syntax_Syntax.lid_and_dd_as_fv
                                          discriminator_name
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
                                              FStar_Compiler_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu___7.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                          [uu___6] in
                                        {
                                          FStar_Syntax_Syntax.lbs1 =
                                            (false, [lb]);
                                          FStar_Syntax_Syntax.lids1 = uu___5
                                        } in
                                      FStar_Syntax_Syntax.Sig_let uu___4 in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu___3;
                                      FStar_Syntax_Syntax.sigrng = p;
                                      FStar_Syntax_Syntax.sigquals = quals;
                                      FStar_Syntax_Syntax.sigmeta =
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs = attrs;
                                      FStar_Syntax_Syntax.sigopens_and_abbrevs
                                        = [];
                                      FStar_Syntax_Syntax.sigopts =
                                        FStar_Pervasives_Native.None
                                    } in
                                  (let uu___4 =
                                     FStar_Compiler_Effect.op_Bang
                                       dbg_LogTypes in
                                   if uu___4
                                   then
                                     let uu___5 =
                                       FStar_Class_Show.show
                                         FStar_Syntax_Print.showable_sigelt
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
                            FStar_Compiler_List.mapi
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
                                               FStar_Pervasives_Native.None in
                                           FStar_Syntax_Syntax.fv_to_tm
                                             uu___5 in
                                         FStar_Syntax_Syntax.mk_Tm_uinst
                                           uu___4 inst_univs in
                                       let proj =
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           field_proj_tm [arg] p in
                                       FStar_Syntax_Syntax.NT (a, proj))
                              fields in
                          let projectors_ses =
                            let uu___ =
                              (FStar_Syntax_Util.has_attribute attrs
                                 FStar_Parser_Const.no_auto_projectors_decls_attr)
                                ||
                                (FStar_Syntax_Util.has_attribute attrs
                                   FStar_Parser_Const.meta_projectors_attr) in
                            if uu___
                            then []
                            else
                              (let uu___2 =
                                 FStar_Compiler_List.mapi
                                   (fun i ->
                                      fun uu___3 ->
                                        match uu___3 with
                                        | {
                                            FStar_Syntax_Syntax.binder_bv = x;
                                            FStar_Syntax_Syntax.binder_qual =
                                              uu___4;
                                            FStar_Syntax_Syntax.binder_positivity
                                              = uu___5;
                                            FStar_Syntax_Syntax.binder_attrs
                                              = uu___6;_}
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
                                              let uu___7 =
                                                FStar_Syntax_Util.arrow
                                                  binders result_comp in
                                              FStar_Syntax_Subst.close_univ_vars
                                                uvs uu___7 in
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
                                                FStar_Compiler_List.filter
                                                  (fun uu___7 ->
                                                     match uu___7 with
                                                     | FStar_Syntax_Syntax.Inline_for_extraction
                                                         -> true
                                                     | FStar_Syntax_Syntax.NoExtract
                                                         -> true
                                                     | FStar_Syntax_Syntax.Private
                                                         -> true
                                                     | uu___8 -> false)
                                                  iquals in
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
                                              let uu___7 =
                                                FStar_Ident.range_of_lid
                                                  field_name in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                                     {
                                                       FStar_Syntax_Syntax.lid2
                                                         = field_name;
                                                       FStar_Syntax_Syntax.us2
                                                         = uvs;
                                                       FStar_Syntax_Syntax.t2
                                                         = t
                                                     });
                                                FStar_Syntax_Syntax.sigrng =
                                                  uu___7;
                                                FStar_Syntax_Syntax.sigquals
                                                  = quals1;
                                                FStar_Syntax_Syntax.sigmeta =
                                                  FStar_Syntax_Syntax.default_sigmeta;
                                                FStar_Syntax_Syntax.sigattrs
                                                  = attrs1;
                                                FStar_Syntax_Syntax.sigopens_and_abbrevs
                                                  = [];
                                                FStar_Syntax_Syntax.sigopts =
                                                  FStar_Pervasives_Native.None
                                              } in
                                            ((let uu___8 =
                                                FStar_Compiler_Effect.op_Bang
                                                  dbg_LogTypes in
                                              if uu___8
                                              then
                                                let uu___9 =
                                                  FStar_Class_Show.show
                                                    FStar_Syntax_Print.showable_sigelt
                                                    decl in
                                                FStar_Compiler_Util.print1
                                                  "Declaration of a projector %s\n"
                                                  uu___9
                                              else ());
                                             if only_decl
                                             then [decl]
                                             else
                                               (let projection =
                                                  let uu___9 =
                                                    FStar_Ident.string_of_id
                                                      x.FStar_Syntax_Syntax.ppname in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    uu___9
                                                    FStar_Pervasives_Native.None
                                                    FStar_Syntax_Syntax.tun in
                                                let arg_pats =
                                                  FStar_Compiler_List.mapi
                                                    (fun j ->
                                                       fun uu___9 ->
                                                         match uu___9 with
                                                         | {
                                                             FStar_Syntax_Syntax.binder_bv
                                                               = x1;
                                                             FStar_Syntax_Syntax.binder_qual
                                                               = imp;
                                                             FStar_Syntax_Syntax.binder_positivity
                                                               = uu___10;
                                                             FStar_Syntax_Syntax.binder_attrs
                                                               = uu___11;_}
                                                             ->
                                                             let b =
                                                               FStar_Syntax_Syntax.is_bqual_implicit
                                                                 imp in
                                                             if
                                                               (i + ntps) = j
                                                             then
                                                               let uu___12 =
                                                                 pos
                                                                   (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                               (uu___12, b)
                                                             else
                                                               if
                                                                 b &&
                                                                   (j < ntps)
                                                               then
                                                                 (let uu___13
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    FStar_Pervasives_Native.None) in
                                                                  (uu___13,
                                                                    b))
                                                               else
                                                                 (let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    x1.FStar_Syntax_Syntax.ppname in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    uu___17
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_var
                                                                    uu___16 in
                                                                    pos
                                                                    uu___15 in
                                                                  (uu___14,
                                                                    b)))
                                                    all_params in
                                                let pat =
                                                  let uu___9 =
                                                    let uu___10 =
                                                      let uu___11 =
                                                        let uu___12 =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            lid
                                                            (FStar_Pervasives_Native.Some
                                                               fvq) in
                                                        (uu___12,
                                                          FStar_Pervasives_Native.None,
                                                          arg_pats) in
                                                      FStar_Syntax_Syntax.Pat_cons
                                                        uu___11 in
                                                    pos uu___10 in
                                                  let uu___10 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      projection in
                                                  (uu___9,
                                                    FStar_Pervasives_Native.None,
                                                    uu___10) in
                                                let body =
                                                  let return_bv =
                                                    FStar_Syntax_Syntax.gen_bv
                                                      "proj_ret"
                                                      (FStar_Pervasives_Native.Some
                                                         p1)
                                                      FStar_Syntax_Syntax.tun in
                                                  let result_typ =
                                                    let uu___9 =
                                                      let uu___10 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          return_bv in
                                                      [uu___10] in
                                                    let uu___10 =
                                                      let uu___11 =
                                                        let uu___12 =
                                                          let uu___13 =
                                                            let uu___14 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                return_bv in
                                                            ((arg_binder.FStar_Syntax_Syntax.binder_bv),
                                                              uu___14) in
                                                          FStar_Syntax_Syntax.NT
                                                            uu___13 in
                                                        [uu___12] in
                                                      FStar_Syntax_Subst.subst
                                                        uu___11
                                                        (FStar_Syntax_Util.comp_result
                                                           result_comp) in
                                                    FStar_Syntax_Subst.close
                                                      uu___9 uu___10 in
                                                  let return_binder =
                                                    let uu___9 =
                                                      let uu___10 =
                                                        let uu___11 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            return_bv in
                                                        [uu___11] in
                                                      FStar_Syntax_Subst.close_binders
                                                        uu___10 in
                                                    FStar_Compiler_List.hd
                                                      uu___9 in
                                                  let returns_annotation =
                                                    let use_eq = true in
                                                    FStar_Pervasives_Native.Some
                                                      (return_binder,
                                                        ((FStar_Pervasives.Inl
                                                            result_typ),
                                                          FStar_Pervasives_Native.None,
                                                          use_eq)) in
                                                  let uu___9 =
                                                    let uu___10 =
                                                      let uu___11 =
                                                        let uu___12 =
                                                          FStar_Syntax_Util.branch
                                                            pat in
                                                        [uu___12] in
                                                      {
                                                        FStar_Syntax_Syntax.scrutinee
                                                          = arg_exp;
                                                        FStar_Syntax_Syntax.ret_opt
                                                          =
                                                          returns_annotation;
                                                        FStar_Syntax_Syntax.brs
                                                          = uu___11;
                                                        FStar_Syntax_Syntax.rc_opt1
                                                          =
                                                          FStar_Pervasives_Native.None
                                                      } in
                                                    FStar_Syntax_Syntax.Tm_match
                                                      uu___10 in
                                                  FStar_Syntax_Syntax.mk
                                                    uu___9 p1 in
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
                                                  let uu___9 =
                                                    let uu___10 =
                                                      FStar_Syntax_Syntax.lid_and_dd_as_fv
                                                        field_name
                                                        FStar_Pervasives_Native.None in
                                                    FStar_Pervasives.Inr
                                                      uu___10 in
                                                  let uu___10 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs imp in
                                                  {
                                                    FStar_Syntax_Syntax.lbname
                                                      = uu___9;
                                                    FStar_Syntax_Syntax.lbunivs
                                                      = uvs;
                                                    FStar_Syntax_Syntax.lbtyp
                                                      = lbtyp;
                                                    FStar_Syntax_Syntax.lbeff
                                                      =
                                                      FStar_Parser_Const.effect_Tot_lid;
                                                    FStar_Syntax_Syntax.lbdef
                                                      = uu___10;
                                                    FStar_Syntax_Syntax.lbattrs
                                                      = [];
                                                    FStar_Syntax_Syntax.lbpos
                                                      =
                                                      FStar_Compiler_Range_Type.dummyRange
                                                  } in
                                                let impl =
                                                  let uu___9 =
                                                    let uu___10 =
                                                      let uu___11 =
                                                        let uu___12 =
                                                          let uu___13 =
                                                            FStar_Compiler_Util.right
                                                              lb.FStar_Syntax_Syntax.lbname in
                                                          (uu___13.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                                        [uu___12] in
                                                      {
                                                        FStar_Syntax_Syntax.lbs1
                                                          = (false, [lb]);
                                                        FStar_Syntax_Syntax.lids1
                                                          = uu___11
                                                      } in
                                                    FStar_Syntax_Syntax.Sig_let
                                                      uu___10 in
                                                  {
                                                    FStar_Syntax_Syntax.sigel
                                                      = uu___9;
                                                    FStar_Syntax_Syntax.sigrng
                                                      = p1;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = quals1;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      =
                                                      FStar_Syntax_Syntax.default_sigmeta;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = attrs1;
                                                    FStar_Syntax_Syntax.sigopens_and_abbrevs
                                                      = [];
                                                    FStar_Syntax_Syntax.sigopts
                                                      =
                                                      FStar_Pervasives_Native.None
                                                  } in
                                                (let uu___10 =
                                                   FStar_Compiler_Effect.op_Bang
                                                     dbg_LogTypes in
                                                 if uu___10
                                                 then
                                                   let uu___11 =
                                                     FStar_Class_Show.show
                                                       FStar_Syntax_Print.showable_sigelt
                                                       impl in
                                                   FStar_Compiler_Util.print1
                                                     "Implementation of a projector %s\n"
                                                     uu___11
                                                 else ());
                                                if no_decl
                                                then [impl]
                                                else [decl; impl]))) fields in
                               FStar_Compiler_List.flatten uu___2) in
                          let no_plugin se =
                            let not_plugin_attr t =
                              let h = FStar_Syntax_Util.head_of t in
                              let uu___ =
                                FStar_Syntax_Util.is_fvar
                                  FStar_Parser_Const.plugin_attr h in
                              Prims.op_Negation uu___ in
                            let uu___ =
                              FStar_Compiler_List.filter not_plugin_attr
                                se.FStar_Syntax_Syntax.sigattrs in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (se.FStar_Syntax_Syntax.sigel);
                              FStar_Syntax_Syntax.sigrng =
                                (se.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (se.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (se.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs = uu___;
                              FStar_Syntax_Syntax.sigopens_and_abbrevs =
                                (se.FStar_Syntax_Syntax.sigopens_and_abbrevs);
                              FStar_Syntax_Syntax.sigopts =
                                (se.FStar_Syntax_Syntax.sigopts)
                            } in
                          FStar_Compiler_List.map no_plugin
                            (FStar_Compiler_List.op_At discriminator_ses
                               projectors_ses)
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
                { FStar_Syntax_Syntax.lid1 = constr_lid;
                  FStar_Syntax_Syntax.us1 = uvs; FStar_Syntax_Syntax.t1 = t;
                  FStar_Syntax_Syntax.ty_lid = typ_lid;
                  FStar_Syntax_Syntax.num_ty_params = n_typars;
                  FStar_Syntax_Syntax.mutuals1 = uu___;
                  FStar_Syntax_Syntax.injective_type_params1 = uu___1;_}
                ->
                let uu___2 = FStar_Syntax_Subst.univ_var_opening uvs in
                (match uu___2 with
                 | (univ_opening, uvs1) ->
                     let t1 = FStar_Syntax_Subst.subst univ_opening t in
                     let uu___3 = FStar_Syntax_Util.arrow_formals t1 in
                     (match uu___3 with
                      | (formals, uu___4) ->
                          let uu___5 =
                            let tps_opt =
                              FStar_Compiler_Util.find_map tcs
                                (fun se1 ->
                                   let uu___6 =
                                     let uu___7 =
                                       let uu___8 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Compiler_Util.must uu___8 in
                                     FStar_Ident.lid_equals typ_lid uu___7 in
                                   if uu___6
                                   then
                                     match se1.FStar_Syntax_Syntax.sigel with
                                     | FStar_Syntax_Syntax.Sig_inductive_typ
                                         { FStar_Syntax_Syntax.lid = uu___7;
                                           FStar_Syntax_Syntax.us = uvs';
                                           FStar_Syntax_Syntax.params = tps;
                                           FStar_Syntax_Syntax.num_uniform_params
                                             = uu___8;
                                           FStar_Syntax_Syntax.t = typ0;
                                           FStar_Syntax_Syntax.mutuals =
                                             uu___9;
                                           FStar_Syntax_Syntax.ds = constrs;
                                           FStar_Syntax_Syntax.injective_type_params
                                             = uu___10;_}
                                         ->
                                         FStar_Pervasives_Native.Some
                                           (tps, typ0,
                                             ((FStar_Compiler_List.length
                                                 constrs)
                                                > Prims.int_one))
                                     | uu___7 -> failwith "Impossible"
                                   else FStar_Pervasives_Native.None) in
                            match tps_opt with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None ->
                                let uu___6 =
                                  FStar_Ident.lid_equals typ_lid
                                    FStar_Parser_Const.exn_lid in
                                if uu___6
                                then ([], FStar_Syntax_Util.ktype0, true)
                                else
                                  FStar_Errors.raise_error
                                    FStar_Syntax_Syntax.has_range_sigelt se
                                    FStar_Errors_Codes.Fatal_UnexpectedDataConstructor
                                    ()
                                    (Obj.magic
                                       FStar_Errors_Msg.is_error_message_string)
                                    (Obj.magic "Unexpected data constructor") in
                          (match uu___5 with
                           | (inductive_tps, typ0, should_refine) ->
                               let inductive_tps1 =
                                 FStar_Syntax_Subst.subst_binders
                                   univ_opening inductive_tps in
                               let typ01 =
                                 let uu___6 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_Compiler_List.length
                                        inductive_tps1) univ_opening in
                                 FStar_Syntax_Subst.subst uu___6 typ0 in
                               let uu___6 =
                                 FStar_Syntax_Util.arrow_formals typ01 in
                               (match uu___6 with
                                | (indices, uu___7) ->
                                    let refine_domain =
                                      let uu___8 =
                                        FStar_Compiler_Util.for_some
                                          (fun uu___9 ->
                                             match uu___9 with
                                             | FStar_Syntax_Syntax.RecordConstructor
                                                 uu___10 -> true
                                             | uu___10 -> false)
                                          se.FStar_Syntax_Syntax.sigquals in
                                      if uu___8 then false else should_refine in
                                    let fv_qual =
                                      let filter_records uu___8 =
                                        match uu___8 with
                                        | FStar_Syntax_Syntax.RecordConstructor
                                            (uu___9, fns) ->
                                            FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Syntax.Record_ctor
                                                 (typ_lid, fns))
                                        | uu___9 ->
                                            FStar_Pervasives_Native.None in
                                      let uu___8 =
                                        FStar_Compiler_Util.find_map
                                          se.FStar_Syntax_Syntax.sigquals
                                          filter_records in
                                      match uu___8 with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Syntax_Syntax.Data_ctor
                                      | FStar_Pervasives_Native.Some q -> q in
                                    let fields =
                                      let uu___8 =
                                        FStar_Compiler_Util.first_N n_typars
                                          formals in
                                      match uu___8 with
                                      | (imp_tps, fields1) ->
                                          let rename =
                                            FStar_Compiler_List.map2
                                              (fun uu___9 ->
                                                 fun uu___10 ->
                                                   match (uu___9, uu___10)
                                                   with
                                                   | ({
                                                        FStar_Syntax_Syntax.binder_bv
                                                          = x;
                                                        FStar_Syntax_Syntax.binder_qual
                                                          = uu___11;
                                                        FStar_Syntax_Syntax.binder_positivity
                                                          = uu___12;
                                                        FStar_Syntax_Syntax.binder_attrs
                                                          = uu___13;_},
                                                      {
                                                        FStar_Syntax_Syntax.binder_bv
                                                          = x';
                                                        FStar_Syntax_Syntax.binder_qual
                                                          = uu___14;
                                                        FStar_Syntax_Syntax.binder_positivity
                                                          = uu___15;
                                                        FStar_Syntax_Syntax.binder_attrs
                                                          = uu___16;_})
                                                       ->
                                                       let uu___17 =
                                                         let uu___18 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x' in
                                                         (x, uu___18) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu___17) imp_tps
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