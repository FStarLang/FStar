open Prims
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.unfold_whnf'
    [FStar_TypeChecker_Normalize.AllowUnboundUniverses]
  
let (tc_tycon :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_TypeChecker_Env.env_t,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universe,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ (tc,uvs,tps,k,mutuals,data) ->
          let env0 = env  in
          let uu____50 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____50 with
           | (usubst,uvs1) ->
               let uu____77 =
                 let uu____84 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                    in
                 let uu____85 = FStar_Syntax_Subst.subst_binders usubst tps
                    in
                 let uu____86 =
                   let uu____87 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____87 k  in
                 (uu____84, uu____85, uu____86)  in
               (match uu____77 with
                | (env1,tps1,k1) ->
                    let uu____105 = FStar_Syntax_Subst.open_term tps1 k1  in
                    (match uu____105 with
                     | (tps2,k2) ->
                         let uu____120 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____120 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____141 =
                                FStar_Syntax_Util.arrow_formals k2  in
                              (match uu____141 with
                               | (indices,t) ->
                                   let uu____180 =
                                     FStar_TypeChecker_TcTerm.tc_binders
                                       env_tps indices
                                      in
                                   (match uu____180 with
                                    | (indices1,env',guard_indices,us') ->
                                        let uu____201 =
                                          let uu____208 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env' t
                                             in
                                          match uu____208 with
                                          | (t1,uu____222,g) ->
                                              let uu____224 =
                                                let uu____225 =
                                                  let uu____226 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      guard_indices g
                                                     in
                                                  FStar_TypeChecker_Env.conj_guard
                                                    guard_params uu____226
                                                   in
                                                FStar_TypeChecker_Rel.discharge_guard
                                                  env' uu____225
                                                 in
                                              (t1, uu____224)
                                           in
                                        (match uu____201 with
                                         | (t1,guard) ->
                                             let k3 =
                                               let uu____246 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   t1
                                                  in
                                               FStar_Syntax_Util.arrow
                                                 indices1 uu____246
                                                in
                                             let uu____249 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____249 with
                                              | (t_type,u) ->
                                                  ((let uu____265 =
                                                      let uu____266 =
                                                        FStar_TypeChecker_Rel.subtype_nosmt
                                                          env1 t1 t_type
                                                         in
                                                      Prims.op_Negation
                                                        uu____266
                                                       in
                                                    if uu____265
                                                    then
                                                      let uu____267 =
                                                        let uu____272 =
                                                          let uu____273 =
                                                            FStar_Syntax_Print.term_to_string
                                                              t1
                                                             in
                                                          let uu____274 =
                                                            FStar_Ident.string_of_lid
                                                              tc
                                                             in
                                                          FStar_Util.format2
                                                            "Type annotation %s for inductive %s is not a subtype of Type"
                                                            uu____273
                                                            uu____274
                                                           in
                                                        (FStar_Errors.Error_InductiveAnnotNotAType,
                                                          uu____272)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____267
                                                        s.FStar_Syntax_Syntax.sigrng
                                                    else ());
                                                   (let usubst1 =
                                                      FStar_Syntax_Subst.univ_var_closing
                                                        uvs1
                                                       in
                                                    let guard1 =
                                                      FStar_TypeChecker_Util.close_guard_implicits
                                                        env1
                                                        (FStar_List.append
                                                           tps3 indices1)
                                                        guard
                                                       in
                                                    let t_tc =
                                                      let uu____287 =
                                                        let uu____294 =
                                                          FStar_All.pipe_right
                                                            tps3
                                                            (FStar_Syntax_Subst.subst_binders
                                                               usubst1)
                                                           in
                                                        let uu____307 =
                                                          let uu____314 =
                                                            let uu____325 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                (FStar_List.length
                                                                   tps3)
                                                                usubst1
                                                               in
                                                            FStar_Syntax_Subst.subst_binders
                                                              uu____325
                                                             in
                                                          FStar_All.pipe_right
                                                            indices1
                                                            uu____314
                                                           in
                                                        FStar_List.append
                                                          uu____294 uu____307
                                                         in
                                                      let uu____342 =
                                                        let uu____345 =
                                                          let uu____346 =
                                                            let uu____351 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                ((FStar_List.length
                                                                    tps3)
                                                                   +
                                                                   (FStar_List.length
                                                                    indices1))
                                                                usubst1
                                                               in
                                                            FStar_Syntax_Subst.subst
                                                              uu____351
                                                             in
                                                          FStar_All.pipe_right
                                                            t1 uu____346
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____345
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____287 uu____342
                                                       in
                                                    let tps4 =
                                                      FStar_Syntax_Subst.close_binders
                                                        tps3
                                                       in
                                                    let k4 =
                                                      FStar_Syntax_Subst.close
                                                        tps4 k3
                                                       in
                                                    let uu____364 =
                                                      let uu____369 =
                                                        FStar_Syntax_Subst.subst_binders
                                                          usubst1 tps4
                                                         in
                                                      let uu____370 =
                                                        let uu____371 =
                                                          FStar_Syntax_Subst.shift_subst
                                                            (FStar_List.length
                                                               tps4) usubst1
                                                           in
                                                        FStar_Syntax_Subst.subst
                                                          uu____371 k4
                                                         in
                                                      (uu____369, uu____370)
                                                       in
                                                    match uu____364 with
                                                    | (tps5,k5) ->
                                                        let fv_tc =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            tc
                                                            FStar_Syntax_Syntax.delta_constant
                                                            FStar_Pervasives_Native.None
                                                           in
                                                        let uu____389 =
                                                          FStar_TypeChecker_Env.push_let_binding
                                                            env0
                                                            (FStar_Util.Inr
                                                               fv_tc)
                                                            (uvs1, t_tc)
                                                           in
                                                        (uu____389,
                                                          (let uu___345_395 =
                                                             s  in
                                                           {
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               (FStar_Syntax_Syntax.Sig_inductive_typ
                                                                  (tc, uvs1,
                                                                    tps5, k5,
                                                                    mutuals,
                                                                    data));
                                                             FStar_Syntax_Syntax.sigrng
                                                               =
                                                               (uu___345_395.FStar_Syntax_Syntax.sigrng);
                                                             FStar_Syntax_Syntax.sigquals
                                                               =
                                                               (uu___345_395.FStar_Syntax_Syntax.sigquals);
                                                             FStar_Syntax_Syntax.sigmeta
                                                               =
                                                               (uu___345_395.FStar_Syntax_Syntax.sigmeta);
                                                             FStar_Syntax_Syntax.sigattrs
                                                               =
                                                               (uu___345_395.FStar_Syntax_Syntax.sigattrs)
                                                           }), u, guard1)))))))))))
      | uu____400 -> failwith "impossible"
  
let (tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun tcs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon (c,_uvs,t,tc_lid,ntps,_mutual_tcs)
            ->
            let uu____460 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____460 with
             | (usubst,_uvs1) ->
                 let uu____483 =
                   let uu____488 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____489 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____488, uu____489)  in
                 (match uu____483 with
                  | (env1,t1) ->
                      let uu____496 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____535  ->
                               match uu____535 with
                               | (se1,u_tc) ->
                                   let uu____550 =
                                     let uu____551 =
                                       let uu____552 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____552  in
                                     FStar_Ident.lid_equals tc_lid uu____551
                                      in
                                   if uu____550
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____571,uu____572,tps,uu____574,uu____575,uu____576)
                                          ->
                                          let tps1 =
                                            let uu____586 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____586
                                              (FStar_List.map
                                                 (fun uu____618  ->
                                                    match uu____618 with
                                                    | (x,uu____630) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____634 =
                                            let uu____641 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____641, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____634
                                      | uu____648 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____689 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____689
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____496 with
                       | (env2,tps,u_tc) ->
                           let uu____714 =
                             let t2 =
                               FStar_TypeChecker_Normalize.unfold_whnf env2
                                 t1
                                in
                             let uu____728 =
                               let uu____729 = FStar_Syntax_Subst.compress t2
                                  in
                               uu____729.FStar_Syntax_Syntax.n  in
                             match uu____728 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____762 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____762 with
                                  | (uu____795,bs') ->
                                      let t3 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (bs', res))
                                          FStar_Pervasives_Native.None
                                          t2.FStar_Syntax_Syntax.pos
                                         in
                                      let subst1 =
                                        FStar_All.pipe_right tps
                                          (FStar_List.mapi
                                             (fun i  ->
                                                fun uu____852  ->
                                                  match uu____852 with
                                                  | (x,uu____858) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____859 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____859)
                             | uu____860 -> ([], t2)  in
                           (match uu____714 with
                            | (arguments,result) ->
                                ((let uu____896 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____896
                                  then
                                    let uu____897 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____898 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____899 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____897 uu____898 uu____899
                                  else ());
                                 (let uu____901 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____901 with
                                  | (arguments1,env',us) ->
                                      let uu____915 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env' result
                                         in
                                      (match uu____915 with
                                       | (result1,res_lcomp) ->
                                           let ty =
                                             let uu____927 =
                                               unfold_whnf env2
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ
                                                in
                                             FStar_All.pipe_right uu____927
                                               FStar_Syntax_Util.unrefine
                                              in
                                           ((let uu____929 =
                                               let uu____930 =
                                                 FStar_Syntax_Subst.compress
                                                   ty
                                                  in
                                               uu____930.FStar_Syntax_Syntax.n
                                                in
                                             match uu____929 with
                                             | FStar_Syntax_Syntax.Tm_type
                                                 uu____933 -> ()
                                             | uu____934 ->
                                                 let uu____935 =
                                                   let uu____940 =
                                                     let uu____941 =
                                                       FStar_Syntax_Print.term_to_string
                                                         result1
                                                        in
                                                     let uu____942 =
                                                       FStar_Syntax_Print.term_to_string
                                                         ty
                                                        in
                                                     FStar_Util.format2
                                                       "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                       uu____941 uu____942
                                                      in
                                                   (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                     uu____940)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____935
                                                   se.FStar_Syntax_Syntax.sigrng);
                                            (let uu____943 =
                                               FStar_Syntax_Util.head_and_args
                                                 result1
                                                in
                                             match uu____943 with
                                             | (head1,uu____963) ->
                                                 let g_uvs =
                                                   let uu____985 =
                                                     let uu____986 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____986.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____985 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       ({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_fvar
                                                            fv;
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____990;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____991;_},tuvs)
                                                       ->
                                                       if
                                                         (FStar_List.length
                                                            _uvs1)
                                                           =
                                                           (FStar_List.length
                                                              tuvs)
                                                       then
                                                         FStar_List.fold_left2
                                                           (fun g  ->
                                                              fun u1  ->
                                                                fun u2  ->
                                                                  let uu____1004
                                                                    =
                                                                    let uu____1005
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____1006
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env'
                                                                    uu____1005
                                                                    uu____1006
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1004)
                                                           FStar_TypeChecker_Env.trivial_guard
                                                           tuvs _uvs1
                                                       else
                                                         failwith
                                                           "Impossible: tc_datacon: length of annotated universes not same as instantiated ones"
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv when
                                                       FStar_Syntax_Syntax.fv_eq_lid
                                                         fv tc_lid
                                                       ->
                                                       FStar_TypeChecker_Env.trivial_guard
                                                   | uu____1009 ->
                                                       let uu____1010 =
                                                         let uu____1015 =
                                                           let uu____1016 =
                                                             FStar_Syntax_Print.lid_to_string
                                                               tc_lid
                                                              in
                                                           let uu____1017 =
                                                             FStar_Syntax_Print.term_to_string
                                                               head1
                                                              in
                                                           FStar_Util.format2
                                                             "Expected a constructor of type %s; got %s"
                                                             uu____1016
                                                             uu____1017
                                                            in
                                                         (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                           uu____1015)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____1010
                                                         se.FStar_Syntax_Syntax.sigrng
                                                    in
                                                 let g =
                                                   FStar_List.fold_left2
                                                     (fun g  ->
                                                        fun uu____1030  ->
                                                          fun u_x  ->
                                                            match uu____1030
                                                            with
                                                            | (x,uu____1037)
                                                                ->
                                                                let uu____1038
                                                                  =
                                                                  FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                   in
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  g
                                                                  uu____1038)
                                                     g_uvs arguments1 us
                                                    in
                                                 let t2 =
                                                   let uu____1042 =
                                                     let uu____1049 =
                                                       FStar_All.pipe_right
                                                         tps
                                                         (FStar_List.map
                                                            (fun uu____1081 
                                                               ->
                                                               match uu____1081
                                                               with
                                                               | (x,uu____1093)
                                                                   ->
                                                                   (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                        in
                                                     FStar_List.append
                                                       uu____1049 arguments1
                                                      in
                                                   let uu____1100 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       result1
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____1042 uu____1100
                                                    in
                                                 let t3 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     _uvs1 t2
                                                    in
                                                 ((let uu___346_1105 = se  in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (c, _uvs1, t3,
                                                            tc_lid, ntps, []));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___346_1105.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___346_1105.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___346_1105.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___346_1105.FStar_Syntax_Syntax.sigattrs)
                                                   }), g))))))))))
        | uu____1108 -> failwith "impossible"
  
let (generalize_and_inst_within :
  FStar_TypeChecker_Env.env_t ->
    FStar_TypeChecker_Env.guard_t ->
      (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universe)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                                   Prims.list)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun g  ->
      fun tcs  ->
        fun datas  ->
          let tc_universe_vars =
            FStar_List.map FStar_Pervasives_Native.snd tcs  in
          let g1 =
            let uu___347_1173 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___347_1173.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___347_1173.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___347_1173.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____1183 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____1183
           then
             let uu____1184 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____1184
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____1220  ->
                     match uu____1220 with
                     | (se,uu____1226) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____1227,uu____1228,tps,k,uu____1231,uu____1232)
                              ->
                              let uu____1241 =
                                let uu____1242 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____1242
                                 in
                              FStar_Syntax_Syntax.null_binder uu____1241
                          | uu____1247 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1271,uu____1272,t,uu____1274,uu____1275,uu____1276)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1281 -> failwith "Impossible"))
              in
           let t =
             let uu____1285 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1285
              in
           (let uu____1293 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____1293
            then
              let uu____1294 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1294
            else ());
           (let uu____1296 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____1296 with
            | (uvs,t1) ->
                ((let uu____1316 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____1316
                  then
                    let uu____1317 =
                      let uu____1318 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____1318
                        (FStar_String.concat ", ")
                       in
                    let uu____1329 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1317 uu____1329
                  else ());
                 (let uu____1331 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____1331 with
                  | (uvs1,t2) ->
                      let uu____1346 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____1346 with
                       | (args,uu____1368) ->
                           let uu____1385 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____1385 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1472  ->
                                       fun uu____1473  ->
                                         match (uu____1472, uu____1473) with
                                         | ((x,uu____1491),(se,uu____1493))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1503,tps,uu____1505,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____1517 =
                                                    let uu____1522 =
                                                      let uu____1523 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____1523.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____1522 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1548 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____1548
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1608
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____1623 -> ([], ty)
                                                     in
                                                  (match uu____1517 with
                                                   | (tps1,t3) ->
                                                       let uu___348_1630 = se
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.sigel
                                                           =
                                                           (FStar_Syntax_Syntax.Sig_inductive_typ
                                                              (tc, uvs1,
                                                                tps1, t3,
                                                                mutuals,
                                                                datas1));
                                                         FStar_Syntax_Syntax.sigrng
                                                           =
                                                           (uu___348_1630.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___348_1630.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___348_1630.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___348_1630.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1635 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1641 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_16  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_16))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___336_1663  ->
                                                match uu___336_1663 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____1669,uu____1670,uu____1671,uu____1672,uu____1673);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1674;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1675;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1676;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1677;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1690 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____1711  ->
                                           fun d  ->
                                             match uu____1711 with
                                             | (t3,uu____1718) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1720,uu____1721,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1730 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____1730
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___349_1731 = d
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___349_1731.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___349_1731.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___349_1731.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___349_1731.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1734 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____1749 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____1749
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____1761 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____1761
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____1777 =
      let uu____1778 = FStar_Syntax_Subst.compress t  in
      uu____1778.FStar_Syntax_Syntax.n  in
    match uu____1777 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1797 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1802 -> failwith "Node is not an fvar or a Tm_uinst"
  
type unfolded_memo_elt =
  (FStar_Ident.lident,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple2 Prims.list
type unfolded_memo_t = unfolded_memo_elt FStar_ST.ref
let (already_unfolded :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ilid  ->
    fun arrghs  ->
      fun unfolded  ->
        fun env  ->
          let uu____1855 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____1924  ->
               match uu____1924 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1959 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____1959  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1855
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____2179 =
             let uu____2180 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____2180
              in
           debug_log env uu____2179);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype
              in
           (let uu____2183 =
              let uu____2184 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____2184
               in
            debug_log env uu____2183);
           (let uu____2187 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2187) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2198 =
                  let uu____2199 = FStar_Syntax_Subst.compress btype1  in
                  uu____2199.FStar_Syntax_Syntax.n  in
                match uu____2198 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2224 = try_get_fv t  in
                    (match uu____2224 with
                     | (fv,us) ->
                         let uu____2231 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2231
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2241  ->
                                 match uu____2241 with
                                 | (t1,uu____2247) ->
                                     let uu____2248 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2248) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let check_comp1 =
                        let c1 =
                          let uu____2294 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____2294
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2298 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____2298
                             (FStar_List.existsb
                                (fun q  ->
                                   q = FStar_Syntax_Syntax.TotalEffect)))
                         in
                      if Prims.op_Negation check_comp1
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2316  ->
                               match uu____2316 with
                               | (b,uu____2322) ->
                                   let uu____2323 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2323) sbs)
                           &&
                           ((let uu____2328 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2328 with
                             | (uu____2333,return_type) ->
                                 let uu____2335 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2335)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2356 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2358 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2361) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2388) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2414,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2472  ->
                          match uu____2472 with
                          | (p,uu____2484,t) ->
                              let bs =
                                let uu____2501 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2501
                                 in
                              let uu____2508 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2508 with
                               | (bs1,t1) ->
                                   let uu____2515 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2515)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2537,uu____2538)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2600 ->
                    ((let uu____2602 =
                        let uu____2603 =
                          let uu____2604 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____2605 =
                            let uu____2606 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____2606  in
                          Prims.strcat uu____2604 uu____2605  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2603
                         in
                      debug_log env uu____2602);
                     false)))))

and (ty_nested_positive_in_inductive :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universes ->
        FStar_Syntax_Syntax.args ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun ilid  ->
      fun us  ->
        fun args  ->
          fun unfolded  ->
            fun env  ->
              (let uu____2624 =
                 let uu____2625 =
                   let uu____2626 =
                     let uu____2627 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____2627  in
                   Prims.strcat ilid.FStar_Ident.str uu____2626  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2625
                  in
               debug_log env uu____2624);
              (let uu____2628 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____2628 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____2641 =
                       FStar_TypeChecker_Env.lookup_attrs_of_lid env ilid  in
                     (match uu____2641 with
                      | FStar_Pervasives_Native.None  ->
                          (debug_log env
                             "Checking nested positivity, not an inductive, return false";
                           false)
                      | FStar_Pervasives_Native.Some [] ->
                          (debug_log env
                             "Checking nested positivity, not an inductive, return false";
                           false)
                      | FStar_Pervasives_Native.Some attrs ->
                          let uu____2657 =
                            FStar_All.pipe_right attrs
                              (FStar_Util.for_some
                                 (fun tm  ->
                                    let uu____2664 =
                                      let uu____2665 =
                                        FStar_Syntax_Subst.compress tm  in
                                      uu____2665.FStar_Syntax_Syntax.n  in
                                    match uu____2664 with
                                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                                        FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.assume_strictly_positive_attr_lid
                                    | uu____2669 -> false))
                             in
                          if uu____2657
                          then
                            ((let uu____2671 =
                                let uu____2672 =
                                  FStar_Ident.string_of_lid ilid  in
                                FStar_Util.format1
                                  "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                                  uu____2672
                                 in
                              debug_log env uu____2671);
                             true)
                          else
                            (debug_log env
                               "Checking nested positivity, not an inductive, return false";
                             false))
                   else
                     (let uu____2676 =
                        already_unfolded ilid args unfolded env  in
                      if uu____2676
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid
                            in
                         (let uu____2701 =
                            let uu____2702 =
                              let uu____2703 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____2703
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2702
                             in
                          debug_log env uu____2701);
                         (let uu____2705 =
                            let uu____2706 = FStar_ST.op_Bang unfolded  in
                            let uu____2756 =
                              let uu____2763 =
                                let uu____2768 =
                                  let uu____2769 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____2769  in
                                (ilid, uu____2768)  in
                              [uu____2763]  in
                            FStar_List.append uu____2706 uu____2756  in
                          FStar_ST.op_Colon_Equals unfolded uu____2705);
                         FStar_List.for_all
                           (fun d  ->
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
  fun ty_lid  ->
    fun dlid  ->
      fun ilid  ->
        fun us  ->
          fun args  ->
            fun num_ibs  ->
              fun unfolded  ->
                fun env  ->
                  debug_log env
                    (Prims.strcat
                       "Checking nested positivity in data constructor "
                       (Prims.strcat dlid.FStar_Ident.str
                          (Prims.strcat " of the inductive "
                             ilid.FStar_Ident.str)));
                  (let uu____2908 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____2908 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____2930 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us;
                        (let dt1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.Eager_unfolding;
                             FStar_TypeChecker_Normalize.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant;
                             FStar_TypeChecker_Normalize.Iota;
                             FStar_TypeChecker_Normalize.Zeta;
                             FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                             env dt
                            in
                         (let uu____2933 =
                            let uu____2934 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____2934
                             in
                          debug_log env uu____2933);
                         (let uu____2935 =
                            let uu____2936 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____2936.FStar_Syntax_Syntax.n  in
                          match uu____2935 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____2958 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____2958 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____3007 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3007 dbs1
                                       in
                                    let c1 =
                                      let uu____3011 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3011 c
                                       in
                                    let uu____3014 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3014 with
                                     | (args1,uu____3042) ->
                                         let subst1 =
                                           FStar_List.fold_left2
                                             (fun subst1  ->
                                                fun ib  ->
                                                  fun arg  ->
                                                    FStar_List.append subst1
                                                      [FStar_Syntax_Syntax.NT
                                                         ((FStar_Pervasives_Native.fst
                                                             ib),
                                                           (FStar_Pervasives_Native.fst
                                                              arg))]) [] ibs1
                                             args1
                                            in
                                         let dbs3 =
                                           FStar_Syntax_Subst.subst_binders
                                             subst1 dbs2
                                            in
                                         let c2 =
                                           let uu____3114 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3114 c1
                                            in
                                         ((let uu____3122 =
                                             let uu____3123 =
                                               let uu____3124 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____3125 =
                                                 let uu____3126 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____3126
                                                  in
                                               Prims.strcat uu____3124
                                                 uu____3125
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3123
                                              in
                                           debug_log env uu____3122);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3155 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3157 =
                                  let uu____3158 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3158.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3157
                                  ilid num_ibs unfolded env))))))

and (ty_nested_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' ->
      FStar_Ident.lident ->
        Prims.int ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun t  ->
      fun ilid  ->
        fun num_ibs  ->
          fun unfolded  ->
            fun env  ->
              match t with
              | FStar_Syntax_Syntax.Tm_app (t1,args) ->
                  (debug_log env
                     "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself";
                   (let uu____3220 = try_get_fv t1  in
                    match uu____3220 with
                    | (fv,uu____3226) ->
                        let uu____3227 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3227
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3248 =
                      let uu____3249 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3249
                       in
                    debug_log env uu____3248);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3251 =
                      FStar_List.fold_left
                        (fun uu____3268  ->
                           fun b  ->
                             match uu____3268 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3289 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3310 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3289, uu____3310))) (true, env)
                        sbs1
                       in
                    match uu____3251 with | (b,uu____3320) -> b))
              | uu____3321 ->
                  failwith "Nested positive check, unhandled case"

let (ty_positive_in_datacon :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.universes ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env -> Prims.bool)
  =
  fun ty_lid  ->
    fun dlid  ->
      fun ty_bs  ->
        fun us  ->
          fun unfolded  ->
            fun env  ->
              let uu____3372 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3372 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3394 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3396 =
                      let uu____3397 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____3397
                       in
                    debug_log env uu____3396);
                   (let uu____3398 =
                      let uu____3399 = FStar_Syntax_Subst.compress dt  in
                      uu____3399.FStar_Syntax_Syntax.n  in
                    match uu____3398 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3402 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3405) ->
                        let dbs1 =
                          let uu____3429 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3429  in
                        let dbs2 =
                          let uu____3467 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3467 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____3472 =
                            let uu____3473 =
                              let uu____3474 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____3474 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3473
                             in
                          debug_log env uu____3472);
                         (let uu____3479 =
                            FStar_List.fold_left
                              (fun uu____3496  ->
                                 fun b  ->
                                   match uu____3496 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3517 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3538 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3517, uu____3538)))
                              (true, env) dbs3
                             in
                          match uu____3479 with | (b,uu____3548) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3549,uu____3550) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3599 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____3617 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____3633,uu____3634,uu____3635) -> (lid, us, bs)
        | uu____3644 -> failwith "Impossible!"  in
      match uu____3617 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____3654 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____3654 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____3677 =
                 let uu____3680 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____3680  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____3692 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3692
                      unfolded_inductives env2) uu____3677)
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3722,uu____3723,t,uu____3725,uu____3726,uu____3727) -> t
    | uu____3732 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____3752 =
         let uu____3753 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____3753 haseq_suffix  in
       uu____3752 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____3773 =
      let uu____3776 =
        let uu____3779 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____3779]  in
      FStar_List.append lid.FStar_Ident.ns uu____3776  in
    FStar_Ident.lid_of_ids uu____3773
  
let (get_optimized_haseq_axiom :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_names ->
          (FStar_Ident.lident,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders,
            FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple5)
  =
  fun en  ->
    fun ty  ->
      fun usubst  ->
        fun us  ->
          let uu____3824 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____3838,bs,t,uu____3841,uu____3842) -> (lid, bs, t)
            | uu____3851 -> failwith "Impossible!"  in
          match uu____3824 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____3873 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____3873 t  in
              let uu____3880 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____3880 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____3898 =
                       let uu____3899 = FStar_Syntax_Subst.compress t2  in
                       uu____3899.FStar_Syntax_Syntax.n  in
                     match uu____3898 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3903) -> ibs
                     | uu____3920 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____3927 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____3928 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____3927 uu____3928
                      in
                   let ind1 =
                     let uu____3934 =
                       let uu____3939 =
                         FStar_List.map
                           (fun uu____3952  ->
                              match uu____3952 with
                              | (bv,aq) ->
                                  let uu____3963 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____3963, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____3939  in
                     uu____3934 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____3969 =
                       let uu____3974 =
                         FStar_List.map
                           (fun uu____3987  ->
                              match uu____3987 with
                              | (bv,aq) ->
                                  let uu____3998 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____3998, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3974  in
                     uu____3969 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____4004 =
                       let uu____4009 =
                         let uu____4010 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____4010]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4009
                        in
                     uu____4004 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4049 =
                            let uu____4050 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4050  in
                          FStar_TypeChecker_Rel.subtype_nosmt en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4049) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4061 =
                              let uu____4064 =
                                let uu____4069 =
                                  let uu____4070 =
                                    let uu____4077 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4077  in
                                  [uu____4070]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4069
                                 in
                              uu____4064 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4061)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___350_4096 = fml  in
                     let uu____4097 =
                       let uu____4098 =
                         let uu____4105 =
                           let uu____4106 =
                             let uu____4117 =
                               let uu____4126 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____4126]  in
                             [uu____4117]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4106  in
                         (fml, uu____4105)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4098  in
                     {
                       FStar_Syntax_Syntax.n = uu____4097;
                       FStar_Syntax_Syntax.pos =
                         (uu___350_4096.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___350_4096.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4171 =
                              let uu____4176 =
                                let uu____4177 =
                                  let uu____4184 =
                                    let uu____4185 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4185 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4184  in
                                [uu____4177]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4176
                               in
                            uu____4171 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4226 =
                              let uu____4231 =
                                let uu____4232 =
                                  let uu____4239 =
                                    let uu____4240 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4240 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4239  in
                                [uu____4232]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4231
                               in
                            uu____4226 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) bs2 fml2
                      in
                   let axiom_lid = get_haseq_axiom_lid lid  in
                   (axiom_lid, fml3, bs2, ibs1, haseq_bs))
  
let (optimized_haseq_soundness_for_data :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term)
  =
  fun ty_lid  ->
    fun data  ->
      fun usubst  ->
        fun bs  ->
          let dt = datacon_typ data  in
          let dt1 = FStar_Syntax_Subst.subst usubst dt  in
          let uu____4300 =
            let uu____4301 = FStar_Syntax_Subst.compress dt1  in
            uu____4301.FStar_Syntax_Syntax.n  in
          match uu____4300 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4305) ->
              let dbs1 =
                let uu____4329 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4329  in
              let dbs2 =
                let uu____4367 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4367 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4382 =
                           let uu____4387 =
                             let uu____4388 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4388]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4387
                            in
                         uu____4382 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4411 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4411 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4419 =
                       let uu____4424 =
                         let uu____4425 =
                           let uu____4432 =
                             let uu____4433 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4433
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4432  in
                         [uu____4425]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4424
                        in
                     uu____4419 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____4466 -> FStar_Syntax_Util.t_true
  
let (optimized_haseq_ty :
  FStar_Syntax_Syntax.sigelts ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        ((FStar_Ident.lident,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2 Prims.list,FStar_TypeChecker_Env.env,
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple4 ->
          FStar_Syntax_Syntax.sigelt ->
            ((FStar_Ident.lident,FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple2 Prims.list,FStar_TypeChecker_Env.env,
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                                    FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple4)
  =
  fun all_datas_in_the_bundle  ->
    fun usubst  ->
      fun us  ->
        fun acc  ->
          fun ty  ->
            let lid =
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,uu____4556,uu____4557,uu____4558,uu____4559,uu____4560)
                  -> lid
              | uu____4569 -> failwith "Impossible!"  in
            let uu____4570 = acc  in
            match uu____4570 with
            | (uu____4607,en,uu____4609,uu____4610) ->
                let uu____4631 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____4631 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____4668 = acc  in
                     (match uu____4668 with
                      | (l_axioms,env,guard',cond') ->
                          let env1 =
                            FStar_TypeChecker_Env.push_binders env bs  in
                          let env2 =
                            FStar_TypeChecker_Env.push_binders env1 ibs  in
                          let t_datas =
                            FStar_List.filter
                              (fun s  ->
                                 match s.FStar_Syntax_Syntax.sigel with
                                 | FStar_Syntax_Syntax.Sig_datacon
                                     (uu____4742,uu____4743,uu____4744,t_lid,uu____4746,uu____4747)
                                     -> t_lid = lid
                                 | uu____4752 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____4765 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____4765)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____4768 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____4771 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____4768, uu____4771)))
  
let (optimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle  ->
    fun tcs  ->
      fun datas  ->
        fun env0  ->
          let us =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4830,us,uu____4832,uu____4833,uu____4834,uu____4835)
                -> us
            | uu____4844 -> failwith "Impossible!"  in
          let uu____4845 = FStar_Syntax_Subst.univ_var_opening us  in
          match uu____4845 with
          | (usubst,us1) ->
              let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
              ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                 "haseq";
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                 env sig_bndle;
               (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                let uu____4870 =
                  FStar_List.fold_left (optimized_haseq_ty datas usubst us1)
                    ([], env1, FStar_Syntax_Util.t_true,
                      FStar_Syntax_Util.t_true) tcs
                   in
                match uu____4870 with
                | (axioms,env2,guard,cond) ->
                    let phi = FStar_Syntax_Util.mk_imp guard cond  in
                    let uu____4948 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi  in
                    (match uu____4948 with
                     | (phi1,uu____4956) ->
                         ((let uu____4958 =
                             FStar_TypeChecker_Env.should_verify env2  in
                           if uu____4958
                           then
                             let uu____4959 =
                               FStar_TypeChecker_Env.guard_of_guard_formula
                                 (FStar_TypeChecker_Common.NonTrivial phi1)
                                in
                             FStar_TypeChecker_Rel.force_trivial_guard env2
                               uu____4959
                           else ());
                          (let ses =
                             FStar_List.fold_left
                               (fun l  ->
                                  fun uu____4976  ->
                                    match uu____4976 with
                                    | (lid,fml) ->
                                        let fml1 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            us1 fml
                                           in
                                        FStar_List.append l
                                          [{
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_assume
                                                  (lid, us1, fml1));
                                             FStar_Syntax_Syntax.sigrng =
                                               FStar_Range.dummyRange;
                                             FStar_Syntax_Syntax.sigquals =
                                               [];
                                             FStar_Syntax_Syntax.sigmeta =
                                               FStar_Syntax_Syntax.default_sigmeta;
                                             FStar_Syntax_Syntax.sigattrs =
                                               []
                                           }]) [] axioms
                              in
                           (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                             "haseq";
                           ses)))))
  
let (unoptimized_haseq_data :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lident Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun usubst  ->
    fun bs  ->
      fun haseq_ind  ->
        fun mutuals  ->
          fun acc  ->
            fun data  ->
              let rec is_mutual t =
                let uu____5044 =
                  let uu____5045 = FStar_Syntax_Subst.compress t  in
                  uu____5045.FStar_Syntax_Syntax.n  in
                match uu____5044 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5052) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5085 = is_mutual t'  in
                    if uu____5085
                    then true
                    else
                      (let uu____5087 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5087)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5103) -> is_mutual t'
                | uu____5108 -> false
              
              and exists_mutual uu___337_5109 =
                match uu___337_5109 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5128 =
                let uu____5129 = FStar_Syntax_Subst.compress dt1  in
                uu____5129.FStar_Syntax_Syntax.n  in
              match uu____5128 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5135) ->
                  let dbs1 =
                    let uu____5159 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5159  in
                  let dbs2 =
                    let uu____5197 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5197 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5215 =
                               let uu____5220 =
                                 let uu____5221 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5221]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5220
                                in
                             uu____5215 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5245 = is_mutual sort  in
                             if uu____5245
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort  in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3
                     in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____5257 =
                             let uu____5262 =
                               let uu____5263 =
                                 let uu____5270 =
                                   let uu____5271 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5271 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____5270  in
                               [uu____5263]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5262
                              in
                           uu____5257 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5304 -> acc
  
let (unoptimized_haseq_ty :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Ident.lident Prims.list ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_name Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun all_datas_in_the_bundle  ->
    fun mutuals  ->
      fun usubst  ->
        fun us  ->
          fun acc  ->
            fun ty  ->
              let uu____5353 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____5375,bs,t,uu____5378,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____5390 -> failwith "Impossible!"  in
              match uu____5353 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____5413 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____5413 t  in
                  let uu____5420 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____5420 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____5430 =
                           let uu____5431 = FStar_Syntax_Subst.compress t2
                              in
                           uu____5431.FStar_Syntax_Syntax.n  in
                         match uu____5430 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____5435) ->
                             ibs
                         | uu____5452 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____5459 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____5460 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____5459
                           uu____5460
                          in
                       let ind1 =
                         let uu____5466 =
                           let uu____5471 =
                             FStar_List.map
                               (fun uu____5484  ->
                                  match uu____5484 with
                                  | (bv,aq) ->
                                      let uu____5495 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5495, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____5471  in
                         uu____5466 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____5501 =
                           let uu____5506 =
                             FStar_List.map
                               (fun uu____5519  ->
                                  match uu____5519 with
                                  | (bv,aq) ->
                                      let uu____5530 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5530, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____5506  in
                         uu____5501 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____5536 =
                           let uu____5541 =
                             let uu____5542 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____5542]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____5541
                            in
                         uu____5536 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____5574,uu____5575,uu____5576,t_lid,uu____5578,uu____5579)
                                  -> t_lid = lid
                              | uu____5584 -> failwith "Impossible")
                           all_datas_in_the_bundle
                          in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas
                          in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind
                          in
                       let fml1 =
                         let uu___351_5594 = fml  in
                         let uu____5595 =
                           let uu____5596 =
                             let uu____5603 =
                               let uu____5604 =
                                 let uu____5615 =
                                   let uu____5624 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____5624]  in
                                 [uu____5615]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____5604
                                in
                             (fml, uu____5603)  in
                           FStar_Syntax_Syntax.Tm_meta uu____5596  in
                         {
                           FStar_Syntax_Syntax.n = uu____5595;
                           FStar_Syntax_Syntax.pos =
                             (uu___351_5594.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___351_5594.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5669 =
                                  let uu____5674 =
                                    let uu____5675 =
                                      let uu____5682 =
                                        let uu____5683 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5683
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5682
                                       in
                                    [uu____5675]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5674
                                   in
                                uu____5669 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5724 =
                                  let uu____5729 =
                                    let uu____5730 =
                                      let uu____5737 =
                                        let uu____5738 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5738
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5737
                                       in
                                    [uu____5730]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5729
                                   in
                                uu____5724 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) bs2 fml2
                          in
                       FStar_Syntax_Util.mk_conj acc fml3)
  
let (unoptimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle  ->
    fun tcs  ->
      fun datas  ->
        fun env0  ->
          let mutuals =
            FStar_List.map
              (fun ty  ->
                 match ty.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____5815,uu____5816,uu____5817,uu____5818,uu____5819)
                     -> lid
                 | uu____5828 -> failwith "Impossible!") tcs
             in
          let uu____5829 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____5841,uu____5842,uu____5843,uu____5844) ->
                (lid, us)
            | uu____5853 -> failwith "Impossible!"  in
          match uu____5829 with
          | (lid,us) ->
              let uu____5862 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5862 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____5889 =
                       let uu____5890 =
                         let uu____5897 = get_haseq_axiom_lid lid  in
                         (uu____5897, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____5890  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5889;
                       FStar_Syntax_Syntax.sigrng = FStar_Range.dummyRange;
                       FStar_Syntax_Syntax.sigquals = [];
                       FStar_Syntax_Syntax.sigmeta =
                         FStar_Syntax_Syntax.default_sigmeta;
                       FStar_Syntax_Syntax.sigattrs = []
                     }  in
                   [se])
  
let (check_inductive_well_typedness :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.sigelt Prims.list,
            FStar_Syntax_Syntax.sigelt Prims.list)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let uu____5950 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___338_5975  ->
                    match uu___338_5975 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____5976;
                        FStar_Syntax_Syntax.sigrng = uu____5977;
                        FStar_Syntax_Syntax.sigquals = uu____5978;
                        FStar_Syntax_Syntax.sigmeta = uu____5979;
                        FStar_Syntax_Syntax.sigattrs = uu____5980;_} -> true
                    | uu____6001 -> false))
             in
          match uu____5950 with
          | (tys,datas) ->
              ((let uu____6023 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___339_6032  ->
                          match uu___339_6032 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6033;
                              FStar_Syntax_Syntax.sigrng = uu____6034;
                              FStar_Syntax_Syntax.sigquals = uu____6035;
                              FStar_Syntax_Syntax.sigmeta = uu____6036;
                              FStar_Syntax_Syntax.sigattrs = uu____6037;_} ->
                              false
                          | uu____6056 -> true))
                   in
                if uu____6023
                then
                  let uu____6057 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6057
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6065 =
                       let uu____6066 = FStar_List.hd tys  in
                       uu____6066.FStar_Syntax_Syntax.sigel  in
                     match uu____6065 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6069,uvs,uu____6071,uu____6072,uu____6073,uu____6074)
                         -> uvs
                     | uu____6083 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6087 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____6113 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____6113 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____6151,bs,t,l1,l2) ->
                                      let uu____6164 =
                                        let uu____6181 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____6182 =
                                          let uu____6183 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____6183
                                            t
                                           in
                                        (lid, univs2, uu____6181, uu____6182,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____6164
                                  | uu____6194 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___352_6195 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___352_6195.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___352_6195.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___352_6195.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___352_6195.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____6205,t,lid_t,x,l) ->
                                      let uu____6214 =
                                        let uu____6229 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____6229, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____6214
                                  | uu____6232 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___353_6233 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___353_6233.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___353_6233.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___353_6233.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___353_6233.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____6234 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____6234, tys1, datas1))
                   in
                match uu____6087 with
                | (env1,tys1,datas1) ->
                    let uu____6260 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____6299  ->
                             match uu____6299 with
                             | (env2,all_tcs,g) ->
                                 let uu____6339 = tc_tycon env2 tc  in
                                 (match uu____6339 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____6366 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____6366
                                        then
                                          let uu____6367 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____6367
                                        else ());
                                       (let uu____6369 =
                                          let uu____6370 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____6370
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____6369))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____6260 with
                     | (env2,tcs,g) ->
                         let uu____6416 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____6438  ->
                                  match uu____6438 with
                                  | (datas2,g1) ->
                                      let uu____6457 =
                                        let uu____6462 = tc_data env2 tcs  in
                                        uu____6462 se  in
                                      (match uu____6457 with
                                       | (data,g') ->
                                           let uu____6479 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____6479)))
                             datas1 ([], g)
                            in
                         (match uu____6416 with
                          | (datas2,g1) ->
                              let uu____6500 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____6518 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____6518, datas2))
                                 in
                              (match uu____6500 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____6550 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____6551 =
                                       FStar_List.collect
                                         (fun s  ->
                                            s.FStar_Syntax_Syntax.sigattrs)
                                         ses
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         (FStar_Syntax_Syntax.Sig_bundle
                                            ((FStar_List.append tcs1 datas3),
                                              lids));
                                       FStar_Syntax_Syntax.sigrng =
                                         uu____6550;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____6551
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____6577,uu____6578)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____6598 =
                                                    let uu____6603 =
                                                      let uu____6604 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____6605 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____6604 uu____6605
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____6603)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____6598
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____6606 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____6606 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____6622)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____6651 ->
                                                             let uu____6652 =
                                                               let uu____6659
                                                                 =
                                                                 let uu____6660
                                                                   =
                                                                   let uu____6673
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____6673)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____6660
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____6659
                                                                in
                                                             uu____6652
                                                               FStar_Pervasives_Native.None
                                                               se.FStar_Syntax_Syntax.sigrng
                                                          in
                                                       (univs2, body)  in
                                                     if
                                                       (FStar_List.length
                                                          univs2)
                                                         =
                                                         (FStar_List.length
                                                            (FStar_Pervasives_Native.fst
                                                               expected_typ1))
                                                     then
                                                       let uu____6695 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____6695 with
                                                        | (uu____6700,inferred)
                                                            ->
                                                            let uu____6702 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____6702
                                                             with
                                                             | (uu____6707,expected)
                                                                 ->
                                                                 let uu____6709
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____6709
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____6712 -> ()));
                                    (sig_bndle, tcs1, datas3)))))))
  
let (early_prims_inductives : Prims.string Prims.list) =
  ["c_False"; "c_True"; "equals"; "h_equals"; "c_and"; "c_or"] 
let (mk_discriminator_and_indexed_projectors :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      Prims.bool ->
        FStar_TypeChecker_Env.env ->
          FStar_Ident.lident ->
            FStar_Ident.lident ->
              FStar_Syntax_Syntax.univ_names ->
                FStar_Syntax_Syntax.binders ->
                  FStar_Syntax_Syntax.binders ->
                    FStar_Syntax_Syntax.binders ->
                      FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun fvq  ->
      fun refine_domain  ->
        fun env  ->
          fun tc  ->
            fun lid  ->
              fun uvs  ->
                fun inductive_tps  ->
                  fun indices  ->
                    fun fields  ->
                      let p = FStar_Ident.range_of_lid lid  in
                      let pos q = FStar_Syntax_Syntax.withinfo q p  in
                      let projectee ptyp =
                        FStar_Syntax_Syntax.gen_bv "projectee"
                          (FStar_Pervasives_Native.Some p) ptyp
                         in
                      let inst_univs =
                        FStar_List.map
                          (fun u  -> FStar_Syntax_Syntax.U_name u) uvs
                         in
                      let tps = inductive_tps  in
                      let arg_typ =
                        let inst_tc =
                          let uu____6804 =
                            let uu____6811 =
                              let uu____6812 =
                                let uu____6819 =
                                  let uu____6822 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____6822  in
                                (uu____6819, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____6812  in
                            FStar_Syntax_Syntax.mk uu____6811  in
                          uu____6804 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____6851  ->
                                  match uu____6851 with
                                  | (x,imp) ->
                                      let uu____6862 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____6862, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____6864 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____6864  in
                      let arg_binder =
                        if Prims.op_Negation refine_domain
                        then unrefined_arg_binder
                        else
                          (let disc_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some p) arg_typ
                              in
                           let sort =
                             let disc_fvar =
                               let uu____6881 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____6881
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____6882 =
                               let uu____6885 =
                                 let uu____6888 =
                                   let uu____6893 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____6894 =
                                     let uu____6895 =
                                       let uu____6902 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____6902
                                        in
                                     [uu____6895]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____6893
                                     uu____6894
                                    in
                                 uu____6888 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____6885  in
                             FStar_Syntax_Util.refine x uu____6882  in
                           let uu____6923 =
                             let uu___354_6924 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___354_6924.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___354_6924.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____6923)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____6939 =
                          FStar_List.map
                            (fun uu____6961  ->
                               match uu____6961 with
                               | (x,uu____6973) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____6939 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7018  ->
                                match uu____7018 with
                                | (x,uu____7030) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____7036 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____7036)
                          &&
                          (((tc.FStar_Ident.ident).FStar_Ident.idText =
                              "dtuple2")
                             ||
                             (FStar_List.existsb
                                (fun s  ->
                                   s =
                                     (tc.FStar_Ident.ident).FStar_Ident.idText)
                                early_prims_inductives))
                         in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let no_decl = false  in
                           let only_decl =
                             early_prims_inductive ||
                               (let uu____7049 =
                                  let uu____7050 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____7050.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____7049)
                              in
                           let quals =
                             let uu____7054 =
                               FStar_List.filter
                                 (fun uu___340_7058  ->
                                    match uu___340_7058 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____7059 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____7054
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____7086 =
                                 let uu____7087 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7087  in
                               FStar_Syntax_Syntax.mk_Total uu____7086  in
                             let uu____7088 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7088
                              in
                           let decl =
                             let uu____7092 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____7092;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____7094 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____7094
                            then
                              let uu____7095 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7095
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
                                          (fun j  ->
                                             fun uu____7146  ->
                                               match uu____7146 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7170 =
                                                       let uu____7173 =
                                                         let uu____7174 =
                                                           let uu____7181 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____7181,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7174
                                                          in
                                                       pos uu____7173  in
                                                     (uu____7170, b)
                                                   else
                                                     (let uu____7187 =
                                                        let uu____7190 =
                                                          let uu____7191 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7191
                                                           in
                                                        pos uu____7190  in
                                                      (uu____7187, b))))
                                      in
                                   let pat_true =
                                     let uu____7209 =
                                       let uu____7212 =
                                         let uu____7213 =
                                           let uu____7226 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____7226, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7213
                                          in
                                       pos uu____7212  in
                                     (uu____7209,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____7260 =
                                       let uu____7263 =
                                         let uu____7264 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7264
                                          in
                                       pos uu____7263  in
                                     (uu____7260,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____7276 =
                                     let uu____7283 =
                                       let uu____7284 =
                                         let uu____7307 =
                                           let uu____7324 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____7339 =
                                             let uu____7356 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____7356]  in
                                           uu____7324 :: uu____7339  in
                                         (arg_exp, uu____7307)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7284
                                        in
                                     FStar_Syntax_Syntax.mk uu____7283  in
                                   uu____7276 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____7435 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____7435
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                       (Prims.parse_int "1"))
                                else
                                  FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")
                                 in
                              let imp =
                                FStar_Syntax_Util.abs binders body
                                  FStar_Pervasives_Native.None
                                 in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun  in
                              let lb =
                                let uu____7449 =
                                  let uu____7454 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____7454  in
                                let uu____7455 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____7449
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____7455 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____7461 =
                                  let uu____7462 =
                                    let uu____7469 =
                                      let uu____7472 =
                                        let uu____7473 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____7473
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____7472]  in
                                    ((false, [lb]), uu____7469)  in
                                  FStar_Syntax_Syntax.Sig_let uu____7462  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7461;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____7485 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____7485
                               then
                                 let uu____7486 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7486
                               else ());
                              [decl; impl]))
                         in
                      let arg_exp =
                        FStar_Syntax_Syntax.bv_to_name
                          (FStar_Pervasives_Native.fst arg_binder)
                         in
                      let binders =
                        FStar_List.append imp_binders [arg_binder]  in
                      let arg =
                        FStar_Syntax_Util.arg_of_non_null_binder arg_binder
                         in
                      let subst1 =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____7538  ->
                                  match uu____7538 with
                                  | (a,uu____7544) ->
                                      let uu____7545 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____7545 with
                                       | (field_name,uu____7551) ->
                                           let field_proj_tm =
                                             let uu____7553 =
                                               let uu____7554 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7554
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7553 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____7575 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7613  ->
                                    match uu____7613 with
                                    | (x,uu____7621) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____7623 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____7623 with
                                         | (field_name,uu____7631) ->
                                             let t =
                                               let uu____7635 =
                                                 let uu____7636 =
                                                   let uu____7639 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7639
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7636
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7635
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____7644 =
                                                    let uu____7645 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____7645.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7644)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7661 =
                                                   FStar_List.filter
                                                     (fun uu___341_7665  ->
                                                        match uu___341_7665
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7666 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7661
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___342_7679  ->
                                                         match uu___342_7679
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____7680 ->
                                                             false))
                                                  in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals1)
                                                in
                                             let attrs =
                                               if only_decl
                                               then []
                                               else
                                                 [FStar_Syntax_Util.attr_substitute]
                                                in
                                             let decl =
                                               let uu____7688 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____7688;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____7690 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____7690
                                               then
                                                 let uu____7691 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____7691
                                               else ());
                                              if only_decl
                                              then [decl]
                                              else
                                                (let projection =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                     FStar_Pervasives_Native.None
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let arg_pats =
                                                   FStar_All.pipe_right
                                                     all_params
                                                     (FStar_List.mapi
                                                        (fun j  ->
                                                           fun uu____7737  ->
                                                             match uu____7737
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp
                                                                    in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____7761
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____7761,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____7777
                                                                    =
                                                                    let uu____7780
                                                                    =
                                                                    let uu____7781
                                                                    =
                                                                    let uu____7788
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____7788,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____7781
                                                                     in
                                                                    pos
                                                                    uu____7780
                                                                     in
                                                                    (uu____7777,
                                                                    b))
                                                                   else
                                                                    (let uu____7794
                                                                    =
                                                                    let uu____7797
                                                                    =
                                                                    let uu____7798
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____7798
                                                                     in
                                                                    pos
                                                                    uu____7797
                                                                     in
                                                                    (uu____7794,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____7816 =
                                                     let uu____7819 =
                                                       let uu____7820 =
                                                         let uu____7833 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____7833,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____7820
                                                        in
                                                     pos uu____7819  in
                                                   let uu____7842 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____7816,
                                                     FStar_Pervasives_Native.None,
                                                     uu____7842)
                                                    in
                                                 let body =
                                                   let uu____7858 =
                                                     let uu____7865 =
                                                       let uu____7866 =
                                                         let uu____7889 =
                                                           let uu____7906 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____7906]  in
                                                         (arg_exp,
                                                           uu____7889)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____7866
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____7865
                                                      in
                                                   uu____7858
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____7974 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____7974
                                                   then
                                                     FStar_Syntax_Syntax.Delta_abstract
                                                       (FStar_Syntax_Syntax.Delta_equational_at_level
                                                          (Prims.parse_int "1"))
                                                   else
                                                     FStar_Syntax_Syntax.Delta_equational_at_level
                                                       (Prims.parse_int "1")
                                                    in
                                                 let lbtyp =
                                                   if no_decl
                                                   then t
                                                   else
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let lb =
                                                   let uu____7985 =
                                                     let uu____7990 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____7990
                                                      in
                                                   let uu____7991 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____7985;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____7991;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____7997 =
                                                     let uu____7998 =
                                                       let uu____8005 =
                                                         let uu____8008 =
                                                           let uu____8009 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____8009
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____8008]  in
                                                       ((false, [lb]),
                                                         uu____8005)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____7998
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____7997;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta;
                                                     FStar_Syntax_Syntax.sigattrs
                                                       = attrs
                                                   }  in
                                                 (let uu____8021 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____8021
                                                  then
                                                    let uu____8022 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8022
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____7575 FStar_List.flatten
                         in
                      FStar_List.append discriminator_ses projectors_ses
  
let (mk_data_operations :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun env  ->
      fun tcs  ->
        fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_datacon
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8070) when
              let uu____8075 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____8075 ->
              let uu____8076 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____8076 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____8098 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____8098 with
                    | (formals,uu____8114) ->
                        let uu____8131 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8163 =
                                   let uu____8164 =
                                     let uu____8165 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____8165  in
                                   FStar_Ident.lid_equals typ_lid uu____8164
                                    in
                                 if uu____8163
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8184,uvs',tps,typ0,uu____8188,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8205 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____8246 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____8246
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____8131 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____8271 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____8271 with
                              | (indices,uu____8287) ->
                                  let refine_domain =
                                    let uu____8305 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___343_8310  ->
                                              match uu___343_8310 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8311 -> true
                                              | uu____8320 -> false))
                                       in
                                    if uu____8305
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___344_8330 =
                                      match uu___344_8330 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8333,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8345 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____8346 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____8346 with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Syntax_Syntax.Data_ctor
                                    | FStar_Pervasives_Native.Some q -> q  in
                                  let iquals1 =
                                    if
                                      (FStar_List.contains
                                         FStar_Syntax_Syntax.Abstract iquals)
                                        &&
                                        (Prims.op_Negation
                                           (FStar_List.contains
                                              FStar_Syntax_Syntax.Private
                                              iquals))
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals  in
                                  let fields =
                                    let uu____8357 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____8357 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8422  ->
                                               fun uu____8423  ->
                                                 match (uu____8422,
                                                         uu____8423)
                                                 with
                                                 | ((x,uu____8441),(x',uu____8443))
                                                     ->
                                                     let uu____8452 =
                                                       let uu____8459 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____8459)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8452) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8464 -> []
  