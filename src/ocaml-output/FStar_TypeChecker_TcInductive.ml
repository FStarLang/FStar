open Prims
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
          let uu____42 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____42 with
           | (usubst,uvs1) ->
               let uu____69 =
                 let uu____76 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                    in
                 let uu____77 = FStar_Syntax_Subst.subst_binders usubst tps
                    in
                 let uu____78 =
                   let uu____79 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____79 k  in
                 (uu____76, uu____77, uu____78)  in
               (match uu____69 with
                | (env1,tps1,k1) ->
                    let uu____97 = FStar_Syntax_Subst.open_term tps1 k1  in
                    (match uu____97 with
                     | (tps2,k2) ->
                         let uu____112 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____112 with
                          | (tps3,env_tps,guard_params,us) ->
                              let k3 =
                                FStar_TypeChecker_Normalize.unfold_whnf env1
                                  k2
                                 in
                              let uu____134 =
                                FStar_Syntax_Util.arrow_formals k3  in
                              (match uu____134 with
                               | (indices,t) ->
                                   let uu____173 =
                                     FStar_TypeChecker_TcTerm.tc_binders
                                       env_tps indices
                                      in
                                   (match uu____173 with
                                    | (indices1,env',guard_indices,us') ->
                                        let uu____194 =
                                          let uu____199 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env' t
                                             in
                                          match uu____199 with
                                          | (t1,uu____211,g) ->
                                              let uu____213 =
                                                let uu____214 =
                                                  let uu____215 =
                                                    FStar_TypeChecker_Rel.conj_guard
                                                      guard_indices g
                                                     in
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    guard_params uu____215
                                                   in
                                                FStar_TypeChecker_Rel.discharge_guard
                                                  env' uu____214
                                                 in
                                              (t1, uu____213)
                                           in
                                        (match uu____194 with
                                         | (t1,guard) ->
                                             let k4 =
                                               let uu____229 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   t1
                                                  in
                                               FStar_Syntax_Util.arrow
                                                 indices1 uu____229
                                                in
                                             let uu____232 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____232 with
                                              | (t_type,u) ->
                                                  let uu____247 =
                                                    let uu____248 =
                                                      FStar_TypeChecker_Rel.teq
                                                        env' t1 t_type
                                                       in
                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                      env' uu____248
                                                     in
                                                  let usubst1 =
                                                    FStar_Syntax_Subst.univ_var_closing
                                                      uvs1
                                                     in
                                                  let t_tc =
                                                    let uu____255 =
                                                      let uu____262 =
                                                        FStar_All.pipe_right
                                                          tps3
                                                          (FStar_Syntax_Subst.subst_binders
                                                             usubst1)
                                                         in
                                                      let uu____269 =
                                                        let uu____276 =
                                                          let uu____280 =
                                                            FStar_Syntax_Subst.shift_subst
                                                              (FStar_List.length
                                                                 tps3)
                                                              usubst1
                                                             in
                                                          FStar_Syntax_Subst.subst_binders
                                                            uu____280
                                                           in
                                                        FStar_All.pipe_right
                                                          indices1 uu____276
                                                         in
                                                      FStar_List.append
                                                        uu____262 uu____269
                                                       in
                                                    let uu____291 =
                                                      let uu____294 =
                                                        let uu____295 =
                                                          let uu____299 =
                                                            FStar_Syntax_Subst.shift_subst
                                                              ((FStar_List.length
                                                                  tps3)
                                                                 +
                                                                 (FStar_List.length
                                                                    indices1))
                                                              usubst1
                                                             in
                                                          FStar_Syntax_Subst.subst
                                                            uu____299
                                                           in
                                                        FStar_All.pipe_right
                                                          t1 uu____295
                                                         in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____294
                                                       in
                                                    FStar_Syntax_Util.arrow
                                                      uu____255 uu____291
                                                     in
                                                  let tps4 =
                                                    FStar_Syntax_Subst.close_binders
                                                      tps3
                                                     in
                                                  let k5 =
                                                    FStar_Syntax_Subst.close
                                                      tps4 k4
                                                     in
                                                  let uu____312 =
                                                    let uu____317 =
                                                      FStar_Syntax_Subst.subst_binders
                                                        usubst1 tps4
                                                       in
                                                    let uu____318 =
                                                      let uu____319 =
                                                        FStar_Syntax_Subst.shift_subst
                                                          (FStar_List.length
                                                             tps4) usubst1
                                                         in
                                                      FStar_Syntax_Subst.subst
                                                        uu____319 k5
                                                       in
                                                    (uu____317, uu____318)
                                                     in
                                                  (match uu____312 with
                                                   | (tps5,k6) ->
                                                       let fv_tc =
                                                         FStar_Syntax_Syntax.lid_as_fv
                                                           tc
                                                           FStar_Syntax_Syntax.Delta_constant
                                                           FStar_Pervasives_Native.None
                                                          in
                                                       let uu____337 =
                                                         FStar_TypeChecker_Env.push_let_binding
                                                           env0
                                                           (FStar_Util.Inr
                                                              fv_tc)
                                                           (uvs1, t_tc)
                                                          in
                                                       (uu____337,
                                                         (let uu___71_343 = s
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              =
                                                              (FStar_Syntax_Syntax.Sig_inductive_typ
                                                                 (tc, uvs1,
                                                                   tps5, k6,
                                                                   mutuals,
                                                                   data));
                                                            FStar_Syntax_Syntax.sigrng
                                                              =
                                                              (uu___71_343.FStar_Syntax_Syntax.sigrng);
                                                            FStar_Syntax_Syntax.sigquals
                                                              =
                                                              (uu___71_343.FStar_Syntax_Syntax.sigquals);
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              (uu___71_343.FStar_Syntax_Syntax.sigmeta);
                                                            FStar_Syntax_Syntax.sigattrs
                                                              =
                                                              (uu___71_343.FStar_Syntax_Syntax.sigattrs)
                                                          }), u, guard))))))))))
      | uu____350 -> failwith "impossible"
  
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
            let uu____410 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____410 with
             | (usubst,_uvs1) ->
                 let uu____433 =
                   let uu____438 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____439 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____438, uu____439)  in
                 (match uu____433 with
                  | (env1,t1) ->
                      let uu____446 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____485  ->
                               match uu____485 with
                               | (se1,u_tc) ->
                                   let uu____500 =
                                     let uu____501 =
                                       let uu____502 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____502  in
                                     FStar_Ident.lid_equals tc_lid uu____501
                                      in
                                   if uu____500
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____521,uu____522,tps,uu____524,uu____525,uu____526)
                                          ->
                                          let tps1 =
                                            let uu____544 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____544
                                              (FStar_List.map
                                                 (fun uu____566  ->
                                                    match uu____566 with
                                                    | (x,uu____578) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____582 =
                                            let uu____589 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____589, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____582
                                      | uu____596 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____637 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____637
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____446 with
                       | (env2,tps,u_tc) ->
                           let uu____668 =
                             let t2 =
                               FStar_TypeChecker_Normalize.unfold_whnf env2
                                 t1
                                in
                             let uu____682 =
                               let uu____683 = FStar_Syntax_Subst.compress t2
                                  in
                               uu____683.FStar_Syntax_Syntax.n  in
                             match uu____682 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____716 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____716 with
                                  | (uu____749,bs') ->
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
                                                fun uu____800  ->
                                                  match uu____800 with
                                                  | (x,uu____806) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____807 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____807)
                             | uu____808 -> ([], t2)  in
                           (match uu____668 with
                            | (arguments,result) ->
                                let uu____841 =
                                  let uu____842 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____842
                                  then
                                    let uu____843 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____844 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____845 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____843 uu____844 uu____845
                                  else ()  in
                                let uu____847 =
                                  FStar_TypeChecker_TcTerm.tc_tparams env2
                                    arguments
                                   in
                                (match uu____847 with
                                 | (arguments1,env',us) ->
                                     let uu____861 =
                                       FStar_TypeChecker_TcTerm.tc_trivial_guard
                                         env' result
                                        in
                                     (match uu____861 with
                                      | (result1,res_lcomp) ->
                                          let uu____872 =
                                            let uu____873 =
                                              let uu____874 =
                                                FStar_Syntax_Subst.compress
                                                  res_lcomp.FStar_Syntax_Syntax.res_typ
                                                 in
                                              uu____874.FStar_Syntax_Syntax.n
                                               in
                                            match uu____873 with
                                            | FStar_Syntax_Syntax.Tm_type
                                                uu____877 -> ()
                                            | ty ->
                                                let uu____879 =
                                                  let uu____884 =
                                                    let uu____885 =
                                                      FStar_Syntax_Print.term_to_string
                                                        result1
                                                       in
                                                    let uu____886 =
                                                      FStar_Syntax_Print.term_to_string
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_Util.format2
                                                      "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                      uu____885 uu____886
                                                     in
                                                  (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                    uu____884)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____879
                                                  se.FStar_Syntax_Syntax.sigrng
                                             in
                                          let uu____887 =
                                            FStar_Syntax_Util.head_and_args
                                              result1
                                             in
                                          (match uu____887 with
                                           | (head1,uu____907) ->
                                               let g_uvs =
                                                 let uu____929 =
                                                   let uu____930 =
                                                     FStar_Syntax_Subst.compress
                                                       head1
                                                      in
                                                   uu____930.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____929 with
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_fvar
                                                          fv;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____934;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____935;_},tuvs)
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
                                                                let uu____948
                                                                  =
                                                                  let uu____949
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                  let uu____950
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
                                                                    uu____949
                                                                    uu____950
                                                                   in
                                                                FStar_TypeChecker_Rel.conj_guard
                                                                  g uu____948)
                                                         FStar_TypeChecker_Rel.trivial_guard
                                                         tuvs _uvs1
                                                     else
                                                       failwith
                                                         "Impossible: tc_datacon: length of annotated universes not same as instantiated ones"
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     fv when
                                                     FStar_Syntax_Syntax.fv_eq_lid
                                                       fv tc_lid
                                                     ->
                                                     FStar_TypeChecker_Rel.trivial_guard
                                                 | uu____953 ->
                                                     let uu____954 =
                                                       let uu____959 =
                                                         let uu____960 =
                                                           FStar_Syntax_Print.lid_to_string
                                                             tc_lid
                                                            in
                                                         let uu____961 =
                                                           FStar_Syntax_Print.term_to_string
                                                             head1
                                                            in
                                                         FStar_Util.format2
                                                           "Expected a constructor of type %s; got %s"
                                                           uu____960
                                                           uu____961
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                         uu____959)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____954
                                                       se.FStar_Syntax_Syntax.sigrng
                                                  in
                                               let g =
                                                 FStar_List.fold_left2
                                                   (fun g  ->
                                                      fun uu____974  ->
                                                        fun u_x  ->
                                                          match uu____974
                                                          with
                                                          | (x,uu____981) ->
                                                              let uu____982 =
                                                                FStar_TypeChecker_Rel.universe_inequality
                                                                  u_x u_tc
                                                                 in
                                                              FStar_TypeChecker_Rel.conj_guard
                                                                g uu____982)
                                                   g_uvs arguments1 us
                                                  in
                                               let t2 =
                                                 let uu____986 =
                                                   let uu____993 =
                                                     FStar_All.pipe_right tps
                                                       (FStar_List.map
                                                          (fun uu____1023  ->
                                                             match uu____1023
                                                             with
                                                             | (x,uu____1035)
                                                                 ->
                                                                 (x,
                                                                   (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                      in
                                                   FStar_List.append
                                                     uu____993 arguments1
                                                    in
                                                 let uu____1044 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     result1
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____986 uu____1044
                                                  in
                                               let t3 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   _uvs1 t2
                                                  in
                                               ((let uu___72_1049 = se  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_datacon
                                                        (c, _uvs1, t3,
                                                          tc_lid, ntps, []));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___72_1049.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___72_1049.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___72_1049.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___72_1049.FStar_Syntax_Syntax.sigattrs)
                                                 }), g))))))))
        | uu____1054 -> failwith "impossible"
  
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
            let uu___73_1119 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___73_1119.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___73_1119.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___73_1119.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____1128 =
            let uu____1129 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____1129
            then
              let uu____1130 = FStar_TypeChecker_Rel.guard_to_string env g1
                 in
              FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
                uu____1130
            else ()  in
          let uu____1132 = FStar_TypeChecker_Rel.force_trivial_guard env g1
             in
          let binders =
            FStar_All.pipe_right tcs
              (FStar_List.map
                 (fun uu____1158  ->
                    match uu____1158 with
                    | (se,uu____1164) ->
                        (match se.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             (uu____1165,uu____1166,tps,k,uu____1169,uu____1170)
                             ->
                             let uu____1179 =
                               let uu____1180 =
                                 FStar_Syntax_Syntax.mk_Total k  in
                               FStar_All.pipe_left
                                 (FStar_Syntax_Util.arrow tps) uu____1180
                                in
                             FStar_Syntax_Syntax.null_binder uu____1179
                         | uu____1187 -> failwith "Impossible")))
             in
          let binders' =
            FStar_All.pipe_right datas
              (FStar_List.map
                 (fun se  ->
                    match se.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____1203,uu____1204,t,uu____1206,uu____1207,uu____1208)
                        -> FStar_Syntax_Syntax.null_binder t
                    | uu____1213 -> failwith "Impossible"))
             in
          let t =
            let uu____1217 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
            FStar_Syntax_Util.arrow (FStar_List.append binders binders')
              uu____1217
             in
          let uu____1220 =
            let uu____1221 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____1221
            then
              let uu____1222 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1222
            else ()  in
          let uu____1224 = FStar_TypeChecker_Util.generalize_universes env t
             in
          match uu____1224 with
          | (uvs,t1) ->
              let uu____1239 =
                let uu____1240 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____1240
                then
                  let uu____1241 =
                    let uu____1242 =
                      FStar_All.pipe_right uvs
                        (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                       in
                    FStar_All.pipe_right uu____1242
                      (FStar_String.concat ", ")
                     in
                  let uu____1253 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                    uu____1241 uu____1253
                else ()  in
              let uu____1255 = FStar_Syntax_Subst.open_univ_vars uvs t1  in
              (match uu____1255 with
               | (uvs1,t2) ->
                   let uu____1270 = FStar_Syntax_Util.arrow_formals t2  in
                   (match uu____1270 with
                    | (args,uu____1292) ->
                        let uu____1309 =
                          FStar_Util.first_N (FStar_List.length binders) args
                           in
                        (match uu____1309 with
                         | (tc_types,data_types) ->
                             let tcs1 =
                               FStar_List.map2
                                 (fun uu____1392  ->
                                    fun uu____1393  ->
                                      match (uu____1392, uu____1393) with
                                      | ((x,uu____1411),(se,uu____1413)) ->
                                          (match se.FStar_Syntax_Syntax.sigel
                                           with
                                           | FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc,uu____1423,tps,uu____1425,mutuals,datas1)
                                               ->
                                               let ty =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs1
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               let uu____1437 =
                                                 let uu____1450 =
                                                   let uu____1451 =
                                                     FStar_Syntax_Subst.compress
                                                       ty
                                                      in
                                                   uu____1451.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____1450 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (binders1,c) ->
                                                     let uu____1484 =
                                                       FStar_Util.first_N
                                                         (FStar_List.length
                                                            tps) binders1
                                                        in
                                                     (match uu____1484 with
                                                      | (tps1,rest) ->
                                                          let t3 =
                                                            match rest with
                                                            | [] ->
                                                                FStar_Syntax_Util.comp_result
                                                                  c
                                                            | uu____1556 ->
                                                                FStar_Syntax_Syntax.mk
                                                                  (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                  FStar_Pervasives_Native.None
                                                                  (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                             in
                                                          (tps1, t3))
                                                 | uu____1579 -> ([], ty)  in
                                               (match uu____1437 with
                                                | (tps1,t3) ->
                                                    let uu___74_1608 = se  in
                                                    {
                                                      FStar_Syntax_Syntax.sigel
                                                        =
                                                        (FStar_Syntax_Syntax.Sig_inductive_typ
                                                           (tc, uvs1, tps1,
                                                             t3, mutuals,
                                                             datas1));
                                                      FStar_Syntax_Syntax.sigrng
                                                        =
                                                        (uu___74_1608.FStar_Syntax_Syntax.sigrng);
                                                      FStar_Syntax_Syntax.sigquals
                                                        =
                                                        (uu___74_1608.FStar_Syntax_Syntax.sigquals);
                                                      FStar_Syntax_Syntax.sigmeta
                                                        =
                                                        (uu___74_1608.FStar_Syntax_Syntax.sigmeta);
                                                      FStar_Syntax_Syntax.sigattrs
                                                        =
                                                        (uu___74_1608.FStar_Syntax_Syntax.sigattrs)
                                                    })
                                           | uu____1621 ->
                                               failwith "Impossible"))
                                 tc_types tcs
                                in
                             let datas1 =
                               match uvs1 with
                               | [] -> datas
                               | uu____1627 ->
                                   let uvs_universes =
                                     FStar_All.pipe_right uvs1
                                       (FStar_List.map
                                          (fun _0_17  ->
                                             FStar_Syntax_Syntax.U_name _0_17))
                                      in
                                   let tc_insts =
                                     FStar_All.pipe_right tcs1
                                       (FStar_List.map
                                          (fun uu___62_1669  ->
                                             match uu___62_1669 with
                                             | {
                                                 FStar_Syntax_Syntax.sigel =
                                                   FStar_Syntax_Syntax.Sig_inductive_typ
                                                   (tc,uu____1677,uu____1678,uu____1679,uu____1680,uu____1681);
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____1682;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = uu____1683;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   = uu____1684;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = uu____1685;_}
                                                 -> (tc, uvs_universes)
                                             | uu____1700 ->
                                                 failwith "Impossible"))
                                      in
                                   FStar_List.map2
                                     (fun uu____1723  ->
                                        fun d  ->
                                          match uu____1723 with
                                          | (t3,uu____1730) ->
                                              (match d.FStar_Syntax_Syntax.sigel
                                               with
                                               | FStar_Syntax_Syntax.Sig_datacon
                                                   (l,uu____1732,uu____1733,tc,ntps,mutuals)
                                                   ->
                                                   let ty =
                                                     let uu____1742 =
                                                       FStar_Syntax_InstFV.instantiate
                                                         tc_insts
                                                         t3.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____1742
                                                       (FStar_Syntax_Subst.close_univ_vars
                                                          uvs1)
                                                      in
                                                   let uu___75_1743 = d  in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (l, uvs1, ty, tc,
                                                            ntps, mutuals));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___75_1743.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___75_1743.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___75_1743.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___75_1743.FStar_Syntax_Syntax.sigattrs)
                                                   }
                                               | uu____1746 ->
                                                   failwith "Impossible"))
                                     data_types datas
                                in
                             (tcs1, datas1))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____1761 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____1761
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____1773 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____1773
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____1789 =
      let uu____1790 = FStar_Syntax_Subst.compress t  in
      uu____1790.FStar_Syntax_Syntax.n  in
    match uu____1789 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1811 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1816 -> failwith "Node is not an fvar or a Tm_uinst"
  
type unfolded_memo_elt =
  (FStar_Ident.lident,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
type unfolded_memo_t = unfolded_memo_elt FStar_ST.ref[@@deriving show]
let (already_unfolded :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ilid  ->
    fun arrghs  ->
      fun unfolded  ->
        fun env  ->
          let uu____1869 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____1938  ->
               match uu____1938 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1973 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____1973  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1869
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          let uu____2192 =
            let uu____2193 =
              let uu____2194 = FStar_Syntax_Print.term_to_string btype  in
              Prims.strcat "Checking strict positivity in type: " uu____2194
               in
            debug_log env uu____2193  in
          let btype1 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta;
              FStar_TypeChecker_Normalize.Eager_unfolding;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant;
              FStar_TypeChecker_Normalize.Iota;
              FStar_TypeChecker_Normalize.Zeta;
              FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype
             in
          let uu____2196 =
            let uu____2197 =
              let uu____2198 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____2198
               in
            debug_log env uu____2197  in
          (let uu____2201 = ty_occurs_in ty_lid btype1  in
           Prims.op_Negation uu____2201) ||
            (let uu____2211 =
               debug_log env "ty does occur in this type, pressing ahead"  in
             let uu____2212 =
               let uu____2213 = FStar_Syntax_Subst.compress btype1  in
               uu____2213.FStar_Syntax_Syntax.n  in
             match uu____2212 with
             | FStar_Syntax_Syntax.Tm_app (t,args) ->
                 let uu____2238 = try_get_fv t  in
                 (match uu____2238 with
                  | (fv,us) ->
                      let uu____2245 =
                        FStar_Ident.lid_equals
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          ty_lid
                         in
                      if uu____2245
                      then
                        let uu____2246 =
                          debug_log env
                            "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments"
                           in
                        FStar_List.for_all
                          (fun uu____2255  ->
                             match uu____2255 with
                             | (t1,uu____2261) ->
                                 let uu____2262 = ty_occurs_in ty_lid t1  in
                                 Prims.op_Negation uu____2262) args
                      else
                        (let uu____2264 =
                           debug_log env
                             "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity"
                            in
                         ty_nested_positive_in_inductive ty_lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           us args unfolded env))
             | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                 let uu____2303 =
                   debug_log env "Checking strict positivity in Tm_arrow"  in
                 let uu____2304 =
                   let uu____2305 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                      in
                   Prims.op_Negation uu____2305  in
                 if uu____2304
                 then
                   let uu____2306 =
                     debug_log env
                       "Checking strict positivity , the arrow is impure, so return true"
                      in
                   true
                 else
                   (let uu____2308 =
                      debug_log env
                        "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type"
                       in
                    (FStar_List.for_all
                       (fun uu____2317  ->
                          match uu____2317 with
                          | (b,uu____2323) ->
                              let uu____2324 =
                                ty_occurs_in ty_lid
                                  b.FStar_Syntax_Syntax.sort
                                 in
                              Prims.op_Negation uu____2324) sbs)
                      &&
                      (let uu____2329 =
                         FStar_Syntax_Subst.open_term sbs
                           (FStar_Syntax_Util.comp_result c)
                          in
                       match uu____2329 with
                       | (uu____2334,return_type) ->
                           let uu____2336 =
                             FStar_TypeChecker_Env.push_binders env sbs  in
                           ty_strictly_positive_in_type ty_lid return_type
                             unfolded uu____2336))
             | FStar_Syntax_Syntax.Tm_fvar uu____2357 ->
                 let uu____2358 =
                   debug_log env
                     "Checking strict positivity in an fvar, return true"
                    in
                 true
             | FStar_Syntax_Syntax.Tm_type uu____2359 ->
                 let uu____2360 =
                   debug_log env
                     "Checking strict positivity in an Tm_type, return true"
                    in
                 true
             | FStar_Syntax_Syntax.Tm_uinst (t,uu____2362) ->
                 let uu____2367 =
                   debug_log env
                     "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)"
                    in
                 ty_strictly_positive_in_type ty_lid t unfolded env
             | FStar_Syntax_Syntax.Tm_refine (bv,uu____2389) ->
                 let uu____2394 =
                   debug_log env
                     "Checking strict positivity in an Tm_refine, recur in the bv sort)"
                    in
                 ty_strictly_positive_in_type ty_lid
                   bv.FStar_Syntax_Syntax.sort unfolded env
             | FStar_Syntax_Syntax.Tm_match (uu____2415,branches) ->
                 let uu____2453 =
                   debug_log env
                     "Checking strict positivity in an Tm_match, recur in the branches)"
                    in
                 FStar_List.for_all
                   (fun uu____2473  ->
                      match uu____2473 with
                      | (p,uu____2485,t) ->
                          let bs =
                            let uu____2498 = FStar_Syntax_Syntax.pat_bvs p
                               in
                            FStar_List.map FStar_Syntax_Syntax.mk_binder
                              uu____2498
                             in
                          let uu____2501 = FStar_Syntax_Subst.open_term bs t
                             in
                          (match uu____2501 with
                           | (bs1,t1) ->
                               let uu____2508 =
                                 FStar_TypeChecker_Env.push_binders env bs1
                                  in
                               ty_strictly_positive_in_type ty_lid t1
                                 unfolded uu____2508)) branches
             | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2530,uu____2531) ->
                 let uu____2572 =
                   debug_log env
                     "Checking strict positivity in an Tm_ascribed, recur)"
                    in
                 ty_strictly_positive_in_type ty_lid t unfolded env
             | uu____2593 ->
                 let uu____2594 =
                   let uu____2595 =
                     let uu____2596 =
                       let uu____2597 = FStar_Syntax_Print.tag_of_term btype1
                          in
                       let uu____2598 =
                         let uu____2599 =
                           FStar_Syntax_Print.term_to_string btype1  in
                         Prims.strcat " and term: " uu____2599  in
                       Prims.strcat uu____2597 uu____2598  in
                     Prims.strcat
                       "Checking strict positivity, unexpected tag: "
                       uu____2596
                      in
                   debug_log env uu____2595  in
                 false)

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
              let uu____2616 =
                let uu____2617 =
                  let uu____2618 =
                    let uu____2619 =
                      let uu____2620 = FStar_Syntax_Print.args_to_string args
                         in
                      Prims.strcat " applied to arguments: " uu____2620  in
                    Prims.strcat ilid.FStar_Ident.str uu____2619  in
                  Prims.strcat "Checking nested positivity in the inductive "
                    uu____2618
                   in
                debug_log env uu____2617  in
              let uu____2621 = FStar_TypeChecker_Env.datacons_of_typ env ilid
                 in
              match uu____2621 with
              | (b,idatas) ->
                  if Prims.op_Negation b
                  then
                    let uu____2634 =
                      debug_log env
                        "Checking nested positivity, not an inductive, return false"
                       in
                    false
                  else
                    (let uu____2636 = already_unfolded ilid args unfolded env
                        in
                     if uu____2636
                     then
                       let uu____2657 =
                         debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args"
                          in
                       true
                     else
                       (let num_ibs =
                          FStar_TypeChecker_Env.num_inductive_ty_params env
                            ilid
                           in
                        let uu____2660 =
                          let uu____2661 =
                            let uu____2662 =
                              let uu____2663 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____2663
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2662
                             in
                          debug_log env uu____2661  in
                        let uu____2664 =
                          let uu____2665 =
                            let uu____2666 = FStar_ST.op_Bang unfolded  in
                            let uu____2716 =
                              let uu____2723 =
                                let uu____2736 =
                                  let uu____2745 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____2745  in
                                (ilid, uu____2736)  in
                              [uu____2723]  in
                            FStar_List.append uu____2666 uu____2716  in
                          FStar_ST.op_Colon_Equals unfolded uu____2665  in
                        FStar_List.for_all
                          (fun d  ->
                             ty_nested_positive_in_dlid ty_lid d ilid us args
                               num_ibs unfolded env) idatas))

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
                  let uu____2907 =
                    debug_log env
                      (Prims.strcat
                         "Checking nested positivity in data constructor "
                         (Prims.strcat dlid.FStar_Ident.str
                            (Prims.strcat " of the inductive "
                               ilid.FStar_Ident.str)))
                     in
                  let uu____2908 =
                    FStar_TypeChecker_Env.lookup_datacon env dlid  in
                  match uu____2908 with
                  | (univ_unif_vars,dt) ->
                      let uu____2915 =
                        FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____2930 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us
                         in
                      let dt1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant;
                          FStar_TypeChecker_Normalize.Iota;
                          FStar_TypeChecker_Normalize.Zeta;
                          FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                          env dt
                         in
                      let uu____2932 =
                        let uu____2933 =
                          let uu____2934 =
                            FStar_Syntax_Print.term_to_string dt1  in
                          Prims.strcat
                            "Checking nested positivity in the data constructor type: "
                            uu____2934
                           in
                        debug_log env uu____2933  in
                      let uu____2935 =
                        let uu____2936 = FStar_Syntax_Subst.compress dt1  in
                        uu____2936.FStar_Syntax_Syntax.n  in
                      (match uu____2935 with
                       | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                           let uu____2957 =
                             debug_log env
                               "Checked nested positivity in Tm_arrow data constructor type"
                              in
                           let uu____2958 = FStar_List.splitAt num_ibs dbs
                              in
                           (match uu____2958 with
                            | (ibs,dbs1) ->
                                let ibs1 =
                                  FStar_Syntax_Subst.open_binders ibs  in
                                let dbs2 =
                                  let uu____3007 =
                                    FStar_Syntax_Subst.opening_of_binders
                                      ibs1
                                     in
                                  FStar_Syntax_Subst.subst_binders uu____3007
                                    dbs1
                                   in
                                let c1 =
                                  let uu____3011 =
                                    FStar_Syntax_Subst.opening_of_binders
                                      ibs1
                                     in
                                  FStar_Syntax_Subst.subst_comp uu____3011 c
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
                                           (FStar_List.length dbs3) subst1
                                          in
                                       FStar_Syntax_Subst.subst_comp
                                         uu____3114 c1
                                        in
                                     let uu____3121 =
                                       let uu____3122 =
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
                                           Prims.strcat uu____3124 uu____3125
                                            in
                                         Prims.strcat
                                           "Checking nested positivity in the unfolded data constructor binders as: "
                                           uu____3123
                                          in
                                       debug_log env uu____3122  in
                                     ty_nested_positive_in_type ty_lid
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (dbs3, c2)) ilid num_ibs unfolded
                                       env))
                       | uu____3147 ->
                           let uu____3148 =
                             debug_log env
                               "Checking nested positivity in the data constructor type that is not an arrow"
                              in
                           let uu____3149 =
                             let uu____3150 = FStar_Syntax_Subst.compress dt1
                                in
                             uu____3150.FStar_Syntax_Syntax.n  in
                           ty_nested_positive_in_type ty_lid uu____3149 ilid
                             num_ibs unfolded env)

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
                  let uu____3211 =
                    debug_log env
                      "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself"
                     in
                  let uu____3212 = try_get_fv t1  in
                  (match uu____3212 with
                   | (fv,uu____3218) ->
                       let uu____3219 =
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           ilid
                          in
                       if uu____3219
                       then true
                       else
                         failwith "Impossible, expected the type to be ilid")
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  let uu____3239 =
                    let uu____3240 =
                      let uu____3241 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3241
                       in
                    debug_log env uu____3240  in
                  let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                  let uu____3243 =
                    FStar_List.fold_left
                      (fun uu____3260  ->
                         fun b  ->
                           match uu____3260 with
                           | (r,env1) ->
                               if Prims.op_Negation r
                               then (r, env1)
                               else
                                 (let uu____3281 =
                                    ty_strictly_positive_in_type ty_lid
                                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                      unfolded env1
                                     in
                                  let uu____3302 =
                                    FStar_TypeChecker_Env.push_binders env1
                                      [b]
                                     in
                                  (uu____3281, uu____3302))) (true, env) sbs1
                     in
                  (match uu____3243 with | (b,uu____3312) -> b)
              | uu____3313 ->
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
              let uu____3364 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3364 with
              | (univ_unif_vars,dt) ->
                  let uu____3371 =
                    FStar_List.iter2
                      (fun u'  ->
                         fun u  ->
                           match u' with
                           | FStar_Syntax_Syntax.U_unif u'' ->
                               FStar_Syntax_Unionfind.univ_change u'' u
                           | uu____3386 ->
                               failwith
                                 "Impossible! Expected universe unification variables")
                      univ_unif_vars us
                     in
                  let uu____3387 =
                    let uu____3388 =
                      let uu____3389 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____3389
                       in
                    debug_log env uu____3388  in
                  let uu____3390 =
                    let uu____3391 = FStar_Syntax_Subst.compress dt  in
                    uu____3391.FStar_Syntax_Syntax.n  in
                  (match uu____3390 with
                   | FStar_Syntax_Syntax.Tm_fvar uu____3394 ->
                       let uu____3395 =
                         debug_log env
                           "Data constructor type is simply an fvar, returning true"
                          in
                       true
                   | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3397) ->
                       let dbs1 =
                         let uu____3421 =
                           FStar_List.splitAt (FStar_List.length ty_bs) dbs
                            in
                         FStar_Pervasives_Native.snd uu____3421  in
                       let dbs2 =
                         let uu____3459 =
                           FStar_Syntax_Subst.opening_of_binders ty_bs  in
                         FStar_Syntax_Subst.subst_binders uu____3459 dbs1  in
                       let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                       let uu____3463 =
                         let uu____3464 =
                           let uu____3465 =
                             let uu____3466 =
                               FStar_Util.string_of_int
                                 (FStar_List.length dbs3)
                                in
                             Prims.strcat uu____3466 " binders"  in
                           Prims.strcat
                             "Data constructor type is an arrow type, so checking strict positivity in "
                             uu____3465
                            in
                         debug_log env uu____3464  in
                       let uu____3471 =
                         FStar_List.fold_left
                           (fun uu____3488  ->
                              fun b  ->
                                match uu____3488 with
                                | (r,env1) ->
                                    if Prims.op_Negation r
                                    then (r, env1)
                                    else
                                      (let uu____3509 =
                                         ty_strictly_positive_in_type ty_lid
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                           unfolded env1
                                          in
                                       let uu____3530 =
                                         FStar_TypeChecker_Env.push_binders
                                           env1 [b]
                                          in
                                       (uu____3509, uu____3530))) (true, env)
                           dbs3
                          in
                       (match uu____3471 with | (b,uu____3540) -> b)
                   | FStar_Syntax_Syntax.Tm_app (uu____3541,uu____3542) ->
                       let uu____3563 =
                         debug_log env
                           "Data constructor type is a Tm_app, so returning true"
                          in
                       true
                   | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                       let uu____3570 =
                         debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type"
                          in
                       ty_strictly_positive_in_type ty_lid t unfolded env
                   | uu____3591 ->
                       failwith
                         "Unexpected data constructor type when checking positivity")
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____3621 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____3637,uu____3638,uu____3639) -> (lid, us, bs)
        | uu____3648 -> failwith "Impossible!"  in
      match uu____3621 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____3658 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____3658 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____3681 =
                 let uu____3684 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____3684  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____3696 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3696
                      unfolded_inductives env2) uu____3681)
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3726,uu____3727,t,uu____3729,uu____3730,uu____3731) -> t
    | uu____3736 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____3756 =
         let uu____3757 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____3757 haseq_suffix  in
       uu____3756 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____3777 =
      let uu____3780 =
        let uu____3783 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____3783]  in
      FStar_List.append lid.FStar_Ident.ns uu____3780  in
    FStar_Ident.lid_of_ids uu____3777
  
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
          let uu____3828 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____3842,bs,t,uu____3845,uu____3846) -> (lid, bs, t)
            | uu____3855 -> failwith "Impossible!"  in
          match uu____3828 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____3877 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____3877 t  in
              let uu____3884 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____3884 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____3908 =
                       let uu____3909 = FStar_Syntax_Subst.compress t2  in
                       uu____3909.FStar_Syntax_Syntax.n  in
                     match uu____3908 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3919) -> ibs
                     | uu____3936 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____3943 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.Delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____3944 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____3943 uu____3944
                      in
                   let ind1 =
                     let uu____3950 =
                       let uu____3953 =
                         FStar_List.map
                           (fun uu____3966  ->
                              match uu____3966 with
                              | (bv,aq) ->
                                  let uu____3977 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____3977, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____3953  in
                     uu____3950 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____3983 =
                       let uu____3986 =
                         FStar_List.map
                           (fun uu____3999  ->
                              match uu____3999 with
                              | (bv,aq) ->
                                  let uu____4010 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4010, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3986  in
                     uu____3983 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____4016 =
                       let uu____4019 =
                         let uu____4020 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____4020]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4019
                        in
                     uu____4016 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4041 =
                            let uu____4042 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4042  in
                          FStar_TypeChecker_Rel.subtype_nosmt en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4041) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4053 =
                              let uu____4054 =
                                let uu____4057 =
                                  let uu____4058 =
                                    let uu____4059 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4059  in
                                  [uu____4058]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4057
                                 in
                              uu____4054 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4053)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___76_4066 = fml  in
                     let uu____4067 =
                       let uu____4068 =
                         let uu____4075 =
                           let uu____4076 =
                             let uu____4087 =
                               let uu____4090 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____4090]  in
                             [uu____4087]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4076  in
                         (fml, uu____4075)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4068  in
                     {
                       FStar_Syntax_Syntax.n = uu____4067;
                       FStar_Syntax_Syntax.pos =
                         (uu___76_4066.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___76_4066.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4103 =
                              let uu____4106 =
                                let uu____4107 =
                                  let uu____4108 =
                                    let uu____4109 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4109 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4108  in
                                [uu____4107]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4106
                               in
                            uu____4103 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4134 =
                              let uu____4137 =
                                let uu____4138 =
                                  let uu____4139 =
                                    let uu____4140 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4140 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4139  in
                                [uu____4138]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4137
                               in
                            uu____4134 FStar_Pervasives_Native.None
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
          let uu____4184 =
            let uu____4185 = FStar_Syntax_Subst.compress dt1  in
            uu____4185.FStar_Syntax_Syntax.n  in
          match uu____4184 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4189) ->
              let dbs1 =
                let uu____4213 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4213  in
              let dbs2 =
                let uu____4251 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4251 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4266 =
                           let uu____4269 =
                             let uu____4270 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4270]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4269
                            in
                         uu____4266 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4275 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4275 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4283 =
                       let uu____4286 =
                         let uu____4287 =
                           let uu____4288 =
                             let uu____4289 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4289
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4288  in
                         [uu____4287]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4286
                        in
                     uu____4283 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____4306 -> FStar_Syntax_Util.t_true
  
let (optimized_haseq_ty :
  FStar_Syntax_Syntax.sigelts ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        ((FStar_Ident.lident,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2 Prims.list,FStar_TypeChecker_Env.env,
          FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
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
                  (lid,uu____4388,uu____4389,uu____4390,uu____4391,uu____4392)
                  -> lid
              | uu____4401 -> failwith "Impossible!"  in
            let uu____4402 = acc  in
            match uu____4402 with
            | (uu____4435,en,uu____4437,uu____4438) ->
                let uu____4451 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____4451 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____4488 = acc  in
                     (match uu____4488 with
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
                                     (uu____4550,uu____4551,uu____4552,t_lid,uu____4554,uu____4555)
                                     -> t_lid = lid
                                 | uu____4560 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____4567 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____4567)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____4568 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____4571 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____4568, uu____4571)))
  
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
                (uu____4630,us,uu____4632,uu____4633,uu____4634,uu____4635)
                -> us
            | uu____4644 -> failwith "Impossible!"  in
          let uu____4645 = FStar_Syntax_Subst.univ_var_opening us  in
          match uu____4645 with
          | (usubst,us1) ->
              let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
              let uu____4667 =
                (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                  "haseq"
                 in
              let uu____4668 =
                (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                  env sig_bndle
                 in
              let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
              let uu____4670 =
                FStar_List.fold_left (optimized_haseq_ty datas usubst us1)
                  ([], env1, FStar_Syntax_Util.t_true,
                    FStar_Syntax_Util.t_true) tcs
                 in
              (match uu____4670 with
               | (axioms,env2,guard,cond) ->
                   let phi = FStar_Syntax_Util.mk_imp guard cond  in
                   let uu____4728 =
                     FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi  in
                   (match uu____4728 with
                    | (phi1,uu____4736) ->
                        let uu____4737 =
                          let uu____4738 =
                            FStar_TypeChecker_Env.should_verify env2  in
                          if uu____4738
                          then
                            let uu____4739 =
                              FStar_TypeChecker_Rel.guard_of_guard_formula
                                (FStar_TypeChecker_Common.NonTrivial phi1)
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard env2
                              uu____4739
                          else ()  in
                        let ses =
                          FStar_List.fold_left
                            (fun l  ->
                               fun uu____4756  ->
                                 match uu____4756 with
                                 | (lid,fml) ->
                                     let fml1 =
                                       FStar_Syntax_Subst.close_univ_vars us1
                                         fml
                                        in
                                     FStar_List.append l
                                       [{
                                          FStar_Syntax_Syntax.sigel =
                                            (FStar_Syntax_Syntax.Sig_assume
                                               (lid, us1, fml1));
                                          FStar_Syntax_Syntax.sigrng =
                                            FStar_Range.dummyRange;
                                          FStar_Syntax_Syntax.sigquals = [];
                                          FStar_Syntax_Syntax.sigmeta =
                                            FStar_Syntax_Syntax.default_sigmeta;
                                          FStar_Syntax_Syntax.sigattrs = []
                                        }]) [] axioms
                           in
                        let uu____4770 =
                          (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                            "haseq"
                           in
                        ses))
  
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
                let uu____4824 =
                  let uu____4825 = FStar_Syntax_Subst.compress t  in
                  uu____4825.FStar_Syntax_Syntax.n  in
                match uu____4824 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____4832) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____4865 = is_mutual t'  in
                    if uu____4865
                    then true
                    else
                      (let uu____4867 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____4867)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____4883) -> is_mutual t'
                | uu____4888 -> false
              
              and exists_mutual uu___63_4889 =
                match uu___63_4889 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____4908 =
                let uu____4909 = FStar_Syntax_Subst.compress dt1  in
                uu____4909.FStar_Syntax_Syntax.n  in
              match uu____4908 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4915) ->
                  let dbs1 =
                    let uu____4939 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____4939  in
                  let dbs2 =
                    let uu____4977 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____4977 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____4995 =
                               let uu____4998 =
                                 let uu____4999 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____4999]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____4998
                                in
                             uu____4995 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5003 = is_mutual sort  in
                             if uu____5003
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
                           let uu____5013 =
                             let uu____5016 =
                               let uu____5017 =
                                 let uu____5018 =
                                   let uu____5019 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5019 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____5018  in
                               [uu____5017]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5016
                              in
                           uu____5013 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5036 -> acc
  
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
              let uu____5085 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____5107,bs,t,uu____5110,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____5122 -> failwith "Impossible!"  in
              match uu____5085 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____5145 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____5145 t  in
                  let uu____5152 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____5152 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____5168 =
                           let uu____5169 = FStar_Syntax_Subst.compress t2
                              in
                           uu____5169.FStar_Syntax_Syntax.n  in
                         match uu____5168 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____5179) ->
                             ibs
                         | uu____5196 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____5203 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____5204 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____5203
                           uu____5204
                          in
                       let ind1 =
                         let uu____5210 =
                           let uu____5213 =
                             FStar_List.map
                               (fun uu____5226  ->
                                  match uu____5226 with
                                  | (bv,aq) ->
                                      let uu____5237 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5237, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____5213  in
                         uu____5210 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____5243 =
                           let uu____5246 =
                             FStar_List.map
                               (fun uu____5259  ->
                                  match uu____5259 with
                                  | (bv,aq) ->
                                      let uu____5270 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5270, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____5246  in
                         uu____5243 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____5276 =
                           let uu____5279 =
                             let uu____5280 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____5280]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____5279
                            in
                         uu____5276 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____5294,uu____5295,uu____5296,t_lid,uu____5298,uu____5299)
                                  -> t_lid = lid
                              | uu____5304 -> failwith "Impossible")
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
                         let uu___77_5310 = fml  in
                         let uu____5311 =
                           let uu____5312 =
                             let uu____5319 =
                               let uu____5320 =
                                 let uu____5331 =
                                   let uu____5334 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____5334]  in
                                 [uu____5331]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____5320
                                in
                             (fml, uu____5319)  in
                           FStar_Syntax_Syntax.Tm_meta uu____5312  in
                         {
                           FStar_Syntax_Syntax.n = uu____5311;
                           FStar_Syntax_Syntax.pos =
                             (uu___77_5310.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___77_5310.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5347 =
                                  let uu____5350 =
                                    let uu____5351 =
                                      let uu____5352 =
                                        let uu____5353 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5353
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5352
                                       in
                                    [uu____5351]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5350
                                   in
                                uu____5347 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5378 =
                                  let uu____5381 =
                                    let uu____5382 =
                                      let uu____5383 =
                                        let uu____5384 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5384
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5383
                                       in
                                    [uu____5382]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5381
                                   in
                                uu____5378 FStar_Pervasives_Native.None
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
                     (lid,uu____5445,uu____5446,uu____5447,uu____5448,uu____5449)
                     -> lid
                 | uu____5458 -> failwith "Impossible!") tcs
             in
          let uu____5459 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____5471,uu____5472,uu____5473,uu____5474) ->
                (lid, us)
            | uu____5483 -> failwith "Impossible!"  in
          match uu____5459 with
          | (lid,us) ->
              let uu____5492 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5492 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____5515 =
                       let uu____5516 =
                         let uu____5523 = get_haseq_axiom_lid lid  in
                         (uu____5523, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____5516  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5515;
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
          let uu____5578 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___64_5603  ->
                    match uu___64_5603 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____5604;
                        FStar_Syntax_Syntax.sigrng = uu____5605;
                        FStar_Syntax_Syntax.sigquals = uu____5606;
                        FStar_Syntax_Syntax.sigmeta = uu____5607;
                        FStar_Syntax_Syntax.sigattrs = uu____5608;_} -> true
                    | uu____5629 -> false))
             in
          match uu____5578 with
          | (tys,datas) ->
              let uu____5650 =
                let uu____5651 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___65_5660  ->
                          match uu___65_5660 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____5661;
                              FStar_Syntax_Syntax.sigrng = uu____5662;
                              FStar_Syntax_Syntax.sigquals = uu____5663;
                              FStar_Syntax_Syntax.sigmeta = uu____5664;
                              FStar_Syntax_Syntax.sigattrs = uu____5665;_} ->
                              false
                          | uu____5684 -> true))
                   in
                if uu____5651
                then
                  let uu____5685 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____5685
                else ()  in
              let univs1 =
                if (FStar_List.length tys) = (Prims.parse_int "0")
                then []
                else
                  (let uu____5693 =
                     let uu____5694 = FStar_List.hd tys  in
                     uu____5694.FStar_Syntax_Syntax.sigel  in
                   match uu____5693 with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (uu____5697,uvs,uu____5699,uu____5700,uu____5701,uu____5702)
                       -> uvs
                   | uu____5711 -> failwith "Impossible, can't happen!")
                 in
              let env0 = env  in
              let uu____5715 =
                if (FStar_List.length univs1) = (Prims.parse_int "0")
                then (env, tys, datas)
                else
                  (let uu____5741 =
                     FStar_Syntax_Subst.univ_var_opening univs1  in
                   match uu____5741 with
                   | (subst1,univs2) ->
                       let tys1 =
                         FStar_List.map
                           (fun se  ->
                              let sigel =
                                match se.FStar_Syntax_Syntax.sigel with
                                | FStar_Syntax_Syntax.Sig_inductive_typ
                                    (lid,uu____5779,bs,t,l1,l2) ->
                                    let uu____5792 =
                                      let uu____5809 =
                                        FStar_Syntax_Subst.subst_binders
                                          subst1 bs
                                         in
                                      let uu____5810 =
                                        let uu____5811 =
                                          FStar_Syntax_Subst.shift_subst
                                            (FStar_List.length bs) subst1
                                           in
                                        FStar_Syntax_Subst.subst uu____5811 t
                                         in
                                      (lid, univs2, uu____5809, uu____5810,
                                        l1, l2)
                                       in
                                    FStar_Syntax_Syntax.Sig_inductive_typ
                                      uu____5792
                                | uu____5824 ->
                                    failwith "Impossible, can't happen"
                                 in
                              let uu___78_5825 = se  in
                              {
                                FStar_Syntax_Syntax.sigel = sigel;
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___78_5825.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___78_5825.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___78_5825.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___78_5825.FStar_Syntax_Syntax.sigattrs)
                              }) tys
                          in
                       let datas1 =
                         FStar_List.map
                           (fun se  ->
                              let sigel =
                                match se.FStar_Syntax_Syntax.sigel with
                                | FStar_Syntax_Syntax.Sig_datacon
                                    (lid,uu____5835,t,lid_t,x,l) ->
                                    let uu____5844 =
                                      let uu____5859 =
                                        FStar_Syntax_Subst.subst subst1 t  in
                                      (lid, univs2, uu____5859, lid_t, x, l)
                                       in
                                    FStar_Syntax_Syntax.Sig_datacon
                                      uu____5844
                                | uu____5864 ->
                                    failwith "Impossible, can't happen"
                                 in
                              let uu___79_5865 = se  in
                              {
                                FStar_Syntax_Syntax.sigel = sigel;
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___79_5865.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___79_5865.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___79_5865.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___79_5865.FStar_Syntax_Syntax.sigattrs)
                              }) datas
                          in
                       let uu____5866 =
                         FStar_TypeChecker_Env.push_univ_vars env univs2  in
                       (uu____5866, tys1, datas1))
                 in
              (match uu____5715 with
               | (env1,tys1,datas1) ->
                   let uu____5892 =
                     FStar_List.fold_right
                       (fun tc  ->
                          fun uu____5931  ->
                            match uu____5931 with
                            | (env2,all_tcs,g) ->
                                let uu____5971 = tc_tycon env2 tc  in
                                (match uu____5971 with
                                 | (env3,tc1,tc_u,guard) ->
                                     let g' =
                                       FStar_TypeChecker_Rel.universe_inequality
                                         FStar_Syntax_Syntax.U_zero tc_u
                                        in
                                     let uu____5997 =
                                       let uu____5998 =
                                         FStar_TypeChecker_Env.debug env3
                                           FStar_Options.Low
                                          in
                                       if uu____5998
                                       then
                                         let uu____5999 =
                                           FStar_Syntax_Print.sigelt_to_string
                                             tc1
                                            in
                                         FStar_Util.print1
                                           "Checked inductive: %s\n"
                                           uu____5999
                                       else ()  in
                                     let uu____6001 =
                                       let uu____6002 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g'
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____6002
                                        in
                                     (env3, ((tc1, tc_u) :: all_tcs),
                                       uu____6001))) tys1
                       (env1, [], FStar_TypeChecker_Rel.trivial_guard)
                      in
                   (match uu____5892 with
                    | (env2,tcs,g) ->
                        let uu____6048 =
                          FStar_List.fold_right
                            (fun se  ->
                               fun uu____6070  ->
                                 match uu____6070 with
                                 | (datas2,g1) ->
                                     let uu____6089 =
                                       let uu____6094 = tc_data env2 tcs  in
                                       uu____6094 se  in
                                     (match uu____6089 with
                                      | (data,g') ->
                                          let uu____6110 =
                                            FStar_TypeChecker_Rel.conj_guard
                                              g1 g'
                                             in
                                          ((data :: datas2), uu____6110)))
                            datas1 ([], g)
                           in
                        (match uu____6048 with
                         | (datas2,g1) ->
                             let uu____6131 =
                               if
                                 (FStar_List.length univs1) =
                                   (Prims.parse_int "0")
                               then
                                 generalize_and_inst_within env1 g1 tcs
                                   datas2
                               else
                                 (let uu____6149 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst tcs
                                     in
                                  (uu____6149, datas2))
                                in
                             (match uu____6131 with
                              | (tcs1,datas3) ->
                                  let sig_bndle =
                                    let uu____6181 =
                                      FStar_TypeChecker_Env.get_range env0
                                       in
                                    let uu____6182 =
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
                                      FStar_Syntax_Syntax.sigrng = uu____6181;
                                      FStar_Syntax_Syntax.sigquals = quals;
                                      FStar_Syntax_Syntax.sigmeta =
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs =
                                        uu____6182
                                    }  in
                                  let uu____6191 =
                                    FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____6208,uu____6209)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____6227 =
                                                    let uu____6232 =
                                                      let uu____6233 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____6234 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____6233 uu____6234
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____6232)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____6227
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____6235 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____6235 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____6251)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____6272 ->
                                                             let uu____6273 =
                                                               let uu____6278
                                                                 =
                                                                 let uu____6279
                                                                   =
                                                                   let uu____6292
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____6292)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____6279
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____6278
                                                                in
                                                             uu____6273
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
                                                       let uu____6298 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____6298 with
                                                        | (uu____6303,inferred)
                                                            ->
                                                            let uu____6305 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____6305
                                                             with
                                                             | (uu____6310,expected)
                                                                 ->
                                                                 let uu____6312
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____6312
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____6315 -> ()))
                                     in
                                  (sig_bndle, tcs1, datas3)))))
  
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
                          let uu____6405 =
                            let uu____6410 =
                              let uu____6411 =
                                let uu____6418 =
                                  let uu____6419 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____6419  in
                                (uu____6418, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____6411  in
                            FStar_Syntax_Syntax.mk uu____6410  in
                          uu____6405 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____6460  ->
                                  match uu____6460 with
                                  | (x,imp) ->
                                      let uu____6471 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____6471, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____6473 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____6473  in
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
                               let uu____6482 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____6482
                                 FStar_Syntax_Syntax.Delta_equational
                                 FStar_Pervasives_Native.None
                                in
                             let uu____6483 =
                               let uu____6484 =
                                 let uu____6485 =
                                   let uu____6488 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____6489 =
                                     let uu____6490 =
                                       let uu____6491 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____6491
                                        in
                                     [uu____6490]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____6488
                                     uu____6489
                                    in
                                 uu____6485 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____6484  in
                             FStar_Syntax_Util.refine x uu____6483  in
                           let uu____6494 =
                             let uu___80_6495 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___80_6495.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___80_6495.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____6494)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____6510 =
                          FStar_List.map
                            (fun uu____6532  ->
                               match uu____6532 with
                               | (x,uu____6544) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____6510 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____6593  ->
                                match uu____6593 with
                                | (x,uu____6605) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____6611 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____6611)
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
                               (let uu____6624 =
                                  let uu____6625 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____6625.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____6624)
                              in
                           let quals =
                             let uu____6629 =
                               FStar_List.filter
                                 (fun uu___66_6633  ->
                                    match uu___66_6633 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____6634 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____6629
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____6655 =
                                 let uu____6656 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____6656  in
                               FStar_Syntax_Syntax.mk_Total uu____6655  in
                             let uu____6657 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____6657
                              in
                           let decl =
                             let uu____6659 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____6659;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           let uu____6660 =
                             let uu____6661 =
                               FStar_TypeChecker_Env.debug env
                                 (FStar_Options.Other "LogTypes")
                                in
                             if uu____6661
                             then
                               let uu____6662 =
                                 FStar_Syntax_Print.sigelt_to_string decl  in
                               FStar_Util.print1
                                 "Declaration of a discriminator %s\n"
                                 uu____6662
                             else ()  in
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
                                             fun uu____6715  ->
                                               match uu____6715 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____6739 =
                                                       let uu____6742 =
                                                         let uu____6743 =
                                                           let uu____6750 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____6750,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____6743
                                                          in
                                                       pos uu____6742  in
                                                     (uu____6739, b)
                                                   else
                                                     (let uu____6754 =
                                                        let uu____6757 =
                                                          let uu____6758 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____6758
                                                           in
                                                        pos uu____6757  in
                                                      (uu____6754, b))))
                                      in
                                   let pat_true =
                                     let uu____6776 =
                                       let uu____6779 =
                                         let uu____6780 =
                                           let uu____6793 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____6793, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____6780
                                          in
                                       pos uu____6779  in
                                     (uu____6776,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____6827 =
                                       let uu____6830 =
                                         let uu____6831 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____6831
                                          in
                                       pos uu____6830  in
                                     (uu____6827,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____6843 =
                                     let uu____6848 =
                                       let uu____6849 =
                                         let uu____6872 =
                                           let uu____6875 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____6876 =
                                             let uu____6879 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____6879]  in
                                           uu____6875 :: uu____6876  in
                                         (arg_exp, uu____6872)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____6849
                                        in
                                     FStar_Syntax_Syntax.mk uu____6848  in
                                   uu____6843 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____6886 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____6886
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    FStar_Syntax_Syntax.Delta_equational
                                else FStar_Syntax_Syntax.Delta_equational  in
                              let imp =
                                FStar_Syntax_Util.abs binders body
                                  FStar_Pervasives_Native.None
                                 in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun  in
                              let lb =
                                let uu____6894 =
                                  let uu____6899 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____6899  in
                                let uu____6900 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____6894
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____6900 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____6906 =
                                  let uu____6907 =
                                    let uu____6914 =
                                      let uu____6917 =
                                        let uu____6918 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____6918
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____6917]  in
                                    ((false, [lb]), uu____6914)  in
                                  FStar_Syntax_Syntax.Sig_let uu____6907  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____6906;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              let uu____6935 =
                                let uu____6936 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "LogTypes")
                                   in
                                if uu____6936
                                then
                                  let uu____6937 =
                                    FStar_Syntax_Print.sigelt_to_string impl
                                     in
                                  FStar_Util.print1
                                    "Implementation of a discriminator %s\n"
                                    uu____6937
                                else ()  in
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
                                fun uu____6979  ->
                                  match uu____6979 with
                                  | (a,uu____6985) ->
                                      let uu____6986 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____6986 with
                                       | (field_name,uu____6992) ->
                                           let field_proj_tm =
                                             let uu____6994 =
                                               let uu____6995 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____6995
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____6994 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____7012 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7044  ->
                                    match uu____7044 with
                                    | (x,uu____7052) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____7054 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____7054 with
                                         | (field_name,uu____7062) ->
                                             let t =
                                               let uu____7064 =
                                                 let uu____7065 =
                                                   let uu____7068 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7068
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7065
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7064
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____7071 =
                                                    let uu____7072 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____7072.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7071)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7087 =
                                                   FStar_List.filter
                                                     (fun uu___67_7091  ->
                                                        match uu___67_7091
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7092 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7087
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___68_7105  ->
                                                         match uu___68_7105
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____7106 ->
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
                                               let uu____7124 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____7124;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             let uu____7125 =
                                               let uu____7126 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____7126
                                               then
                                                 let uu____7127 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____7127
                                               else ()  in
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
                                                          fun uu____7175  ->
                                                            match uu____7175
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
                                                                  let uu____7199
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                  (uu____7199,
                                                                    b)
                                                                else
                                                                  if
                                                                    b &&
                                                                    (j < ntps)
                                                                  then
                                                                    (
                                                                    let uu____7215
                                                                    =
                                                                    let uu____7218
                                                                    =
                                                                    let uu____7219
                                                                    =
                                                                    let uu____7226
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____7226,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____7219
                                                                     in
                                                                    pos
                                                                    uu____7218
                                                                     in
                                                                    (uu____7215,
                                                                    b))
                                                                  else
                                                                    (
                                                                    let uu____7230
                                                                    =
                                                                    let uu____7233
                                                                    =
                                                                    let uu____7234
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____7234
                                                                     in
                                                                    pos
                                                                    uu____7233
                                                                     in
                                                                    (uu____7230,
                                                                    b))))
                                                   in
                                                let pat =
                                                  let uu____7250 =
                                                    let uu____7253 =
                                                      let uu____7254 =
                                                        let uu____7267 =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            lid
                                                            FStar_Syntax_Syntax.Delta_constant
                                                            (FStar_Pervasives_Native.Some
                                                               fvq)
                                                           in
                                                        (uu____7267,
                                                          arg_pats)
                                                         in
                                                      FStar_Syntax_Syntax.Pat_cons
                                                        uu____7254
                                                       in
                                                    pos uu____7253  in
                                                  let uu____7276 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      projection
                                                     in
                                                  (uu____7250,
                                                    FStar_Pervasives_Native.None,
                                                    uu____7276)
                                                   in
                                                let body =
                                                  let uu____7288 =
                                                    let uu____7293 =
                                                      let uu____7294 =
                                                        let uu____7317 =
                                                          let uu____7320 =
                                                            FStar_Syntax_Util.branch
                                                              pat
                                                             in
                                                          [uu____7320]  in
                                                        (arg_exp, uu____7317)
                                                         in
                                                      FStar_Syntax_Syntax.Tm_match
                                                        uu____7294
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      uu____7293
                                                     in
                                                  uu____7288
                                                    FStar_Pervasives_Native.None
                                                    p1
                                                   in
                                                let imp =
                                                  FStar_Syntax_Util.abs
                                                    binders body
                                                    FStar_Pervasives_Native.None
                                                   in
                                                let dd =
                                                  let uu____7328 =
                                                    FStar_All.pipe_right
                                                      quals1
                                                      (FStar_List.contains
                                                         FStar_Syntax_Syntax.Abstract)
                                                     in
                                                  if uu____7328
                                                  then
                                                    FStar_Syntax_Syntax.Delta_abstract
                                                      FStar_Syntax_Syntax.Delta_equational
                                                  else
                                                    FStar_Syntax_Syntax.Delta_equational
                                                   in
                                                let lbtyp =
                                                  if no_decl
                                                  then t
                                                  else
                                                    FStar_Syntax_Syntax.tun
                                                   in
                                                let lb =
                                                  let uu____7335 =
                                                    let uu____7340 =
                                                      FStar_Syntax_Syntax.lid_as_fv
                                                        field_name dd
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    FStar_Util.Inr uu____7340
                                                     in
                                                  let uu____7341 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs imp
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.lbname
                                                      = uu____7335;
                                                    FStar_Syntax_Syntax.lbunivs
                                                      = uvs;
                                                    FStar_Syntax_Syntax.lbtyp
                                                      = lbtyp;
                                                    FStar_Syntax_Syntax.lbeff
                                                      =
                                                      FStar_Parser_Const.effect_Tot_lid;
                                                    FStar_Syntax_Syntax.lbdef
                                                      = uu____7341;
                                                    FStar_Syntax_Syntax.lbattrs
                                                      = [];
                                                    FStar_Syntax_Syntax.lbpos
                                                      =
                                                      FStar_Range.dummyRange
                                                  }  in
                                                let impl =
                                                  let uu____7347 =
                                                    let uu____7348 =
                                                      let uu____7355 =
                                                        let uu____7358 =
                                                          let uu____7359 =
                                                            FStar_All.pipe_right
                                                              lb.FStar_Syntax_Syntax.lbname
                                                              FStar_Util.right
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7359
                                                            (fun fv  ->
                                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                           in
                                                        [uu____7358]  in
                                                      ((false, [lb]),
                                                        uu____7355)
                                                       in
                                                    FStar_Syntax_Syntax.Sig_let
                                                      uu____7348
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.sigel
                                                      = uu____7347;
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
                                                let uu____7376 =
                                                  let uu____7377 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____7377
                                                  then
                                                    let uu____7378 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____7378
                                                  else ()  in
                                                if no_decl
                                                then [impl]
                                                else [decl; impl]))))
                           in
                        FStar_All.pipe_right uu____7012 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____7426) when
              let uu____7431 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____7431 ->
              let uu____7432 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____7432 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____7454 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____7454 with
                    | (formals,uu____7470) ->
                        let uu____7487 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____7519 =
                                   let uu____7520 =
                                     let uu____7521 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____7521  in
                                   FStar_Ident.lid_equals typ_lid uu____7520
                                    in
                                 if uu____7519
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____7540,uvs',tps,typ0,uu____7544,constrs)
                                       ->
                                       let uu____7554 = ()  in
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____7561 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____7602 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____7602
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____7487 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____7635 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____7635 with
                              | (indices,uu____7651) ->
                                  let refine_domain =
                                    let uu____7669 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___69_7674  ->
                                              match uu___69_7674 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____7675 -> true
                                              | uu____7684 -> false))
                                       in
                                    if uu____7669
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___70_7693 =
                                      match uu___70_7693 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____7696,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____7708 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____7709 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____7709 with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Syntax_Syntax.Data_ctor
                                    | FStar_Pervasives_Native.Some q -> q  in
                                  let iquals1 =
                                    if
                                      FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract iquals
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals  in
                                  let fields =
                                    let uu____7720 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____7720 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____7785  ->
                                               fun uu____7786  ->
                                                 match (uu____7785,
                                                         uu____7786)
                                                 with
                                                 | ((x,uu____7804),(x',uu____7806))
                                                     ->
                                                     let uu____7815 =
                                                       let uu____7822 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____7822)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____7815) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____7823 -> []
  