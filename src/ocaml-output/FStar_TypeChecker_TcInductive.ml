open Prims
let tc_tycon:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_TypeChecker_Env.env_t* FStar_Syntax_Syntax.sigelt*
        FStar_Syntax_Syntax.universe* FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (tc,uvs,tps,k,mutuals,data,quals,r) ->
          let uu____34 = FStar_Syntax_Subst.open_term tps k in
          (match uu____34 with
           | (tps,k) ->
               let uu____43 = FStar_TypeChecker_TcTerm.tc_binders env tps in
               (match uu____43 with
                | (tps,env_tps,guard_params,us) ->
                    let uu____56 = FStar_Syntax_Util.arrow_formals k in
                    (match uu____56 with
                     | (indices,t) ->
                         let uu____80 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices in
                         (match uu____80 with
                          | (indices,env',guard_indices,us') ->
                              let uu____93 =
                                let uu____96 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t in
                                match uu____96 with
                                | (t,uu____103,g) ->
                                    let uu____105 =
                                      let uu____106 =
                                        let uu____107 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____107 in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____106 in
                                    (t, uu____105) in
                              (match uu____93 with
                               | (t,guard) ->
                                   let k =
                                     let uu____117 =
                                       FStar_Syntax_Syntax.mk_Total t in
                                     FStar_Syntax_Util.arrow indices
                                       uu____117 in
                                   let uu____120 =
                                     FStar_Syntax_Util.type_u () in
                                   (match uu____120 with
                                    | (t_type,u) ->
                                        ((let uu____130 =
                                            FStar_TypeChecker_Rel.teq env' t
                                              t_type in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____130);
                                         (let t_tc =
                                            let uu____134 =
                                              FStar_Syntax_Syntax.mk_Total t in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps indices)
                                              uu____134 in
                                          let tps =
                                            FStar_Syntax_Subst.close_binders
                                              tps in
                                          let k =
                                            FStar_Syntax_Subst.close tps k in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              None in
                                          let uu____142 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc) in
                                          (uu____142,
                                            (FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc, [], tps, k, mutuals,
                                                 data, quals, r)), u, guard)))))))))
      | uu____150 -> failwith "impossible"
let tc_data:
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt* FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt* FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun tcs  ->
      fun uu___76_175  ->
        match uu___76_175 with
        | FStar_Syntax_Syntax.Sig_datacon
            (c,_uvs,t,tc_lid,ntps,quals,_mutual_tcs,r) ->
            let uu____191 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____205  ->
                     match uu____205 with
                     | (se,u_tc) ->
                         let uu____214 =
                           let uu____215 =
                             let uu____216 =
                               FStar_Syntax_Util.lid_of_sigelt se in
                             FStar_Util.must uu____216 in
                           FStar_Ident.lid_equals tc_lid uu____215 in
                         if uu____214
                         then
                           (match se with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____226,uu____227,tps,uu____229,uu____230,uu____231,uu____232,uu____233)
                                ->
                                let tps =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____254  ->
                                          match uu____254 with
                                          | (x,uu____261) ->
                                              (x,
                                                (Some
                                                   FStar_Syntax_Syntax.imp_tag)))) in
                                let tps = FStar_Syntax_Subst.open_binders tps in
                                let uu____264 =
                                  let uu____268 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps in
                                  (uu____268, tps, u_tc) in
                                Some uu____264
                            | uu____272 -> failwith "Impossible")
                         else None) in
              match tps_u_opt with
              | Some x -> x
              | None  ->
                  if FStar_Ident.lid_equals tc_lid FStar_Syntax_Const.exn_lid
                  then (env, [], FStar_Syntax_Syntax.U_zero)
                  else
                    Prims.raise
                      (FStar_Errors.Error ("Unexpected data constructor", r)) in
            (match uu____191 with
             | (env,tps,u_tc) ->
                 let uu____311 =
                   let uu____319 =
                     let uu____320 = FStar_Syntax_Subst.compress t in
                     uu____320.FStar_Syntax_Syntax.n in
                   match uu____319 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____342 = FStar_Util.first_N ntps bs in
                       (match uu____342 with
                        | (uu____360,bs') ->
                            let t =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_arrow (bs', res)))
                                None t.FStar_Syntax_Syntax.pos in
                            let subst =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____396  ->
                                        match uu____396 with
                                        | (x,uu____400) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x))) in
                            let uu____401 = FStar_Syntax_Subst.subst subst t in
                            FStar_Syntax_Util.arrow_formals uu____401)
                   | uu____402 -> ([], t) in
                 (match uu____311 with
                  | (arguments,result) ->
                      ((let uu____423 =
                          FStar_TypeChecker_Env.debug env FStar_Options.Low in
                        if uu____423
                        then
                          let uu____424 = FStar_Syntax_Print.lid_to_string c in
                          let uu____425 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments in
                          let uu____426 =
                            FStar_Syntax_Print.term_to_string result in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____424
                            uu____425 uu____426
                        else ());
                       (let uu____428 =
                          FStar_TypeChecker_TcTerm.tc_tparams env arguments in
                        match uu____428 with
                        | (arguments,env',us) ->
                            let uu____437 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result in
                            (match uu____437 with
                             | (result,res_lcomp) ->
                                 ((let uu____445 =
                                     let uu____446 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ in
                                     uu____446.FStar_Syntax_Syntax.n in
                                   match uu____445 with
                                   | FStar_Syntax_Syntax.Tm_type uu____449 ->
                                       ()
                                   | ty ->
                                       let uu____451 =
                                         let uu____452 =
                                           let uu____455 =
                                             let uu____456 =
                                               FStar_Syntax_Print.term_to_string
                                                 result in
                                             let uu____457 =
                                               FStar_Syntax_Print.term_to_string
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ in
                                             FStar_Util.format2
                                               "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                               uu____456 uu____457 in
                                           (uu____455, r) in
                                         FStar_Errors.Error uu____452 in
                                       Prims.raise uu____451);
                                  (let uu____458 =
                                     FStar_Syntax_Util.head_and_args result in
                                   match uu____458 with
                                   | (head,uu____471) ->
                                       ((let uu____487 =
                                           let uu____488 =
                                             FStar_Syntax_Subst.compress head in
                                           uu____488.FStar_Syntax_Syntax.n in
                                         match uu____487 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____492 ->
                                             let uu____493 =
                                               let uu____494 =
                                                 let uu____497 =
                                                   let uu____498 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       tc_lid in
                                                   let uu____499 =
                                                     FStar_Syntax_Print.term_to_string
                                                       head in
                                                   FStar_Util.format2
                                                     "Expected a constructor of type %s; got %s"
                                                     uu____498 uu____499 in
                                                 (uu____497, r) in
                                               FStar_Errors.Error uu____494 in
                                             Prims.raise uu____493);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____504  ->
                                                  fun u_x  ->
                                                    match uu____504 with
                                                    | (x,uu____509) ->
                                                        let uu____510 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____510)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments us in
                                         let t =
                                           let uu____514 =
                                             let uu____518 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____532  ->
                                                       match uu____532 with
                                                       | (x,uu____539) ->
                                                           (x,
                                                             (Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true))))) in
                                             FStar_List.append uu____518
                                               arguments in
                                           let uu____544 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result in
                                           FStar_Syntax_Util.arrow uu____514
                                             uu____544 in
                                         ((FStar_Syntax_Syntax.Sig_datacon
                                             (c, [], t, tc_lid, ntps, quals,
                                               [], r)), g))))))))))
        | uu____552 -> failwith "impossible"
let generalize_and_inst_within:
  FStar_TypeChecker_Env.env_t ->
    FStar_TypeChecker_Env.guard_t ->
      (FStar_Syntax_Syntax.sigelt* FStar_Syntax_Syntax.universe) Prims.list
        ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
            Prims.list)
  =
  fun env  ->
    fun g  ->
      fun tcs  ->
        fun datas  ->
          let tc_universe_vars = FStar_List.map Prims.snd tcs in
          let g =
            let uu___82_588 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___82_588.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___82_588.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (Prims.snd g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___82_588.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____594 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____594
           then
             let uu____595 = FStar_TypeChecker_Rel.guard_to_string env g in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____595
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____606  ->
                     match uu____606 with
                     | (se,uu____610) ->
                         (match se with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____611,uu____612,tps,k,uu____615,uu____616,uu____617,uu____618)
                              ->
                              let uu____625 =
                                let uu____626 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____626 in
                              FStar_Syntax_Syntax.null_binder uu____625
                          | uu____633 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun uu___77_638  ->
                     match uu___77_638 with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____639,uu____640,t,uu____642,uu____643,uu____644,uu____645,uu____646)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____651 -> failwith "Impossible")) in
           let t =
             let uu____655 =
               FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____655 in
           (let uu____659 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____659
            then
              let uu____660 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____660
            else ());
           (let uu____662 = FStar_TypeChecker_Util.generalize_universes env t in
            match uu____662 with
            | (uvs,t) ->
                ((let uu____672 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____672
                  then
                    let uu____673 =
                      let uu____674 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____674
                        (FStar_String.concat ", ") in
                    let uu____680 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____673 uu____680
                  else ());
                 (let uu____682 = FStar_Syntax_Subst.open_univ_vars uvs t in
                  match uu____682 with
                  | (uvs,t) ->
                      let uu____691 = FStar_Syntax_Util.arrow_formals t in
                      (match uu____691 with
                       | (args,uu____704) ->
                           let uu____715 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
                           (match uu____715 with
                            | (tc_types,data_types) ->
                                let tcs =
                                  FStar_List.map2
                                    (fun uu____752  ->
                                       fun uu____753  ->
                                         match (uu____752, uu____753) with
                                         | ((x,uu____763),(se,uu____765)) ->
                                             (match se with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____771,tps,uu____773,mutuals,datas,quals,r)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____785 =
                                                    let uu____793 =
                                                      let uu____794 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____794.FStar_Syntax_Syntax.n in
                                                    match uu____793 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders,c) ->
                                                        let uu____816 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders in
                                                        (match uu____816 with
                                                         | (tps,rest) ->
                                                             let t =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____859 ->
                                                                   let uu____863
                                                                    =
                                                                    FStar_ST.read
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
                                                                   (FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c)))
                                                                    uu____863
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps, t))
                                                    | uu____886 -> ([], ty) in
                                                  (match uu____785 with
                                                   | (tps,t) ->
                                                       FStar_Syntax_Syntax.Sig_inductive_typ
                                                         (tc, uvs, tps, t,
                                                           mutuals, datas,
                                                           quals, r))
                                              | uu____912 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas =
                                  match uvs with
                                  | [] -> datas
                                  | uu____916 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs
                                          (FStar_List.map
                                             (fun _0_28  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_28)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs
                                          (FStar_List.map
                                             (fun uu___78_933  ->
                                                match uu___78_933 with
                                                | FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc,uu____938,uu____939,uu____940,uu____941,uu____942,uu____943,uu____944)
                                                    -> (tc, uvs_universes)
                                                | uu____952 ->
                                                    failwith "Impossible")) in
                                      FStar_List.map2
                                        (fun uu____958  ->
                                           fun d  ->
                                             match uu____958 with
                                             | (t,uu____963) ->
                                                 (match d with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____965,uu____966,tc,ntps,quals,mutuals,r)
                                                      ->
                                                      let ty =
                                                        let uu____977 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____977
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs) in
                                                      FStar_Syntax_Syntax.Sig_datacon
                                                        (l, uvs, ty, tc,
                                                          ntps, quals,
                                                          mutuals, r)
                                                  | uu____980 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs, datas)))))))
let debug_log: FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____989 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____989
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let ty_occurs_in:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____997 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____997
let try_get_fv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv* FStar_Syntax_Syntax.universes)
  =
  fun t  ->
    let uu____1006 =
      let uu____1007 = FStar_Syntax_Subst.compress t in
      uu____1007.FStar_Syntax_Syntax.n in
    match uu____1006 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
        (match t.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1023 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1026 -> failwith "Node is not an fvar or a Tm_uinst"
type unfolded_memo_elt =
  (FStar_Ident.lident* FStar_Syntax_Syntax.args) Prims.list
type unfolded_memo_t = unfolded_memo_elt FStar_ST.ref
let already_unfolded:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ilid  ->
    fun arrghs  ->
      fun unfolded  ->
        fun env  ->
          let uu____1045 = FStar_ST.read unfolded in
          FStar_List.existsML
            (fun uu____1057  ->
               match uu____1057 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1077 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        Prims.fst uu____1077 in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (Prims.fst a) (Prims.fst a'))) true args
                        l)) uu____1045
let rec ty_strictly_positive_in_type:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1172 =
             let uu____1173 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____1173 in
           debug_log env uu____1172);
          (let btype =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____1176 =
              let uu____1177 = FStar_Syntax_Print.term_to_string btype in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1177 in
            debug_log env uu____1176);
           (let uu____1178 = ty_occurs_in ty_lid btype in
            Prims.op_Negation uu____1178) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1180 =
                  let uu____1181 = FStar_Syntax_Subst.compress btype in
                  uu____1181.FStar_Syntax_Syntax.n in
                match uu____1180 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1200 = try_get_fv t in
                    (match uu____1200 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1212  ->
                                 match uu____1212 with
                                 | (t,uu____1216) ->
                                     let uu____1217 = ty_occurs_in ty_lid t in
                                     Prims.op_Negation uu____1217) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____1237 =
                        let uu____1238 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____1238 in
                      if uu____1237
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____1244  ->
                               match uu____1244 with
                               | (b,uu____1248) ->
                                   let uu____1249 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____1249) sbs)
                           &&
                           ((let uu____1250 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____1250 with
                             | (uu____1253,return_type) ->
                                 let uu____1255 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____1255)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____1256 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____1258 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____1261) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____1268) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____1274,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____1309  ->
                          match uu____1309 with
                          | (p,uu____1317,t) ->
                              let bs =
                                let uu____1327 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____1327 in
                              let uu____1329 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____1329 with
                               | (bs,t) ->
                                   let uu____1334 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs in
                                   ty_strictly_positive_in_type ty_lid t
                                     unfolded uu____1334)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1336,uu____1337)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____1357 ->
                    ((let uu____1359 =
                        let uu____1360 =
                          let uu____1361 =
                            FStar_Syntax_Print.tag_of_term btype in
                          let uu____1362 =
                            let uu____1363 =
                              FStar_Syntax_Print.term_to_string btype in
                            Prims.strcat " and term: " uu____1363 in
                          Prims.strcat uu____1361 uu____1362 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____1360 in
                      debug_log env uu____1359);
                     false)))))
and ty_nested_positive_in_inductive:
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universes ->
        FStar_Syntax_Syntax.args ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun ilid  ->
      fun us  ->
        fun args  ->
          fun unfolded  ->
            fun env  ->
              (let uu____1371 =
                 let uu____1372 =
                   let uu____1373 =
                     let uu____1374 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____1374 in
                   Prims.strcat ilid.FStar_Ident.str uu____1373 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____1372 in
               debug_log env uu____1371);
              (let uu____1375 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____1375 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____1385 =
                        already_unfolded ilid args unfolded env in
                      if uu____1385
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____1390 =
                            let uu____1391 =
                              let uu____1392 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____1392
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____1391 in
                          debug_log env uu____1390);
                         (let uu____1394 =
                            let uu____1395 = FStar_ST.read unfolded in
                            let uu____1399 =
                              let uu____1403 =
                                let uu____1411 =
                                  let uu____1417 =
                                    FStar_List.splitAt num_ibs args in
                                  Prims.fst uu____1417 in
                                (ilid, uu____1411) in
                              [uu____1403] in
                            FStar_List.append uu____1395 uu____1399 in
                          FStar_ST.write unfolded uu____1394);
                         FStar_List.for_all
                           (fun d  ->
                              ty_nested_positive_in_dlid ty_lid d ilid us
                                args num_ibs unfolded env) idatas)))
and ty_nested_positive_in_dlid:
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            Prims.int ->
              unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
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
                  (let uu____1475 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____1475 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Unionfind.change u'' (Some u)
                               | uu____1487 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us;
                        (let dt =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.Eager_unfolding;
                             FStar_TypeChecker_Normalize.UnfoldUntil
                               FStar_Syntax_Syntax.Delta_constant;
                             FStar_TypeChecker_Normalize.Iota;
                             FStar_TypeChecker_Normalize.Zeta;
                             FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                             env dt in
                         (let uu____1490 =
                            let uu____1491 =
                              FStar_Syntax_Print.term_to_string dt in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____1491 in
                          debug_log env uu____1490);
                         (let uu____1492 =
                            let uu____1493 = FStar_Syntax_Subst.compress dt in
                            uu____1493.FStar_Syntax_Syntax.n in
                          match uu____1492 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____1509 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____1509 with
                                | (ibs,dbs) ->
                                    let ibs =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs =
                                      let uu____1536 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____1536 dbs in
                                    let c =
                                      let uu____1539 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____1539 c in
                                    let uu____1541 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____1541 with
                                     | (args,uu____1559) ->
                                         let subst =
                                           FStar_List.fold_left2
                                             (fun subst  ->
                                                fun ib  ->
                                                  fun arg  ->
                                                    FStar_List.append subst
                                                      [FStar_Syntax_Syntax.NT
                                                         ((Prims.fst ib),
                                                           (Prims.fst arg))])
                                             [] ibs args in
                                         let dbs =
                                           FStar_Syntax_Subst.subst_binders
                                             subst dbs in
                                         let c =
                                           let uu____1605 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs) subst in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____1605 c in
                                         ((let uu____1613 =
                                             let uu____1614 =
                                               let uu____1615 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs in
                                               let uu____1616 =
                                                 let uu____1617 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c in
                                                 Prims.strcat ", and c: "
                                                   uu____1617 in
                                               Prims.strcat uu____1615
                                                 uu____1616 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____1614 in
                                           debug_log env uu____1613);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs, c)) ilid num_ibs
                                            unfolded env))))
                          | uu____1618 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____1620 =
                                  let uu____1621 =
                                    FStar_Syntax_Subst.compress dt in
                                  uu____1621.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____1620
                                  ilid num_ibs unfolded env))))))
and ty_nested_positive_in_type:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' ->
      FStar_Ident.lident ->
        Prims.int ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun t  ->
      fun ilid  ->
        fun num_ibs  ->
          fun unfolded  ->
            fun env  ->
              match t with
              | FStar_Syntax_Syntax.Tm_app (t,args) ->
                  (debug_log env
                     "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself";
                   (let uu____1647 = try_get_fv t in
                    match uu____1647 with
                    | (fv,uu____1651) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____1670 =
                      let uu____1671 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____1671 in
                    debug_log env uu____1670);
                   (let uu____1672 =
                      FStar_List.fold_left
                        (fun uu____1679  ->
                           fun b  ->
                             match uu____1679 with
                             | (r,env) ->
                                 if Prims.op_Negation r
                                 then (r, env)
                                 else
                                   (let uu____1692 =
                                      ty_strictly_positive_in_type ty_lid
                                        (Prims.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env in
                                    let uu____1693 =
                                      FStar_TypeChecker_Env.push_binders env
                                        [b] in
                                    (uu____1692, uu____1693))) (true, env)
                        sbs in
                    match uu____1672 with | (b,uu____1699) -> b))
              | uu____1700 ->
                  failwith "Nested positive check, unhandled case"
let ty_positive_in_datacon:
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.universes ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env -> Prims.bool
  =
  fun ty_lid  ->
    fun dlid  ->
      fun ty_bs  ->
        fun us  ->
          fun unfolded  ->
            fun env  ->
              let uu____1719 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____1719 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Unionfind.change u'' (Some u)
                          | uu____1731 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____1733 =
                      let uu____1734 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____1734 in
                    debug_log env uu____1733);
                   (let uu____1735 =
                      let uu____1736 = FStar_Syntax_Subst.compress dt in
                      uu____1736.FStar_Syntax_Syntax.n in
                    match uu____1735 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____1739 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1742) ->
                        let dbs =
                          let uu____1757 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          Prims.snd uu____1757 in
                        let dbs =
                          let uu____1779 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____1779 dbs in
                        let dbs = FStar_Syntax_Subst.open_binders dbs in
                        ((let uu____1783 =
                            let uu____1784 =
                              let uu____1785 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs) in
                              Prims.strcat uu____1785 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____1784 in
                          debug_log env uu____1783);
                         (let uu____1791 =
                            FStar_List.fold_left
                              (fun uu____1798  ->
                                 fun b  ->
                                   match uu____1798 with
                                   | (r,env) ->
                                       if Prims.op_Negation r
                                       then (r, env)
                                       else
                                         (let uu____1811 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (Prims.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env in
                                          let uu____1812 =
                                            FStar_TypeChecker_Env.push_binders
                                              env [b] in
                                          (uu____1811, uu____1812)))
                              (true, env) dbs in
                          match uu____1791 with | (b,uu____1818) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____1819,uu____1820) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | uu____1836 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let check_positivity:
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env_t -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____1854 =
        match ty with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____1864,uu____1865,uu____1866,uu____1867,uu____1868)
            -> (lid, us, bs)
        | uu____1875 -> failwith "Impossible!" in
      match uu____1854 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____1882 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____1882 with
           | (ty_usubst,ty_us) ->
               let env = FStar_TypeChecker_Env.push_univ_vars env ty_us in
               let env = FStar_TypeChecker_Env.push_binders env ty_bs in
               let ty_bs = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs = FStar_Syntax_Subst.open_binders ty_bs in
               let uu____1897 =
                 let uu____1899 =
                   FStar_TypeChecker_Env.datacons_of_typ env ty_lid in
                 Prims.snd uu____1899 in
               FStar_List.for_all
                 (fun d  ->
                    let uu____1905 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us in
                    ty_positive_in_datacon ty_lid d ty_bs uu____1905
                      unfolded_inductives env) uu____1897)
let datacon_typ: FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1912,uu____1913,t,uu____1915,uu____1916,uu____1917,uu____1918,uu____1919)
        -> t
    | uu____1924 -> failwith "Impossible!"
let optimized_haseq_soundness_for_data:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term
  =
  fun ty_lid  ->
    fun data  ->
      fun usubst  ->
        fun bs  ->
          let dt = datacon_typ data in
          let dt = FStar_Syntax_Subst.subst usubst dt in
          let uu____1941 =
            let uu____1942 = FStar_Syntax_Subst.compress dt in
            uu____1942.FStar_Syntax_Syntax.n in
          match uu____1941 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1946) ->
              let dbs =
                let uu____1961 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                Prims.snd uu____1961 in
              let dbs =
                let uu____1983 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____1983 dbs in
              let dbs = FStar_Syntax_Subst.open_binders dbs in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____1992 =
                           let uu____1993 =
                             let uu____1994 =
                               FStar_Syntax_Syntax.as_arg
                                 (Prims.fst b).FStar_Syntax_Syntax.sort in
                             [uu____1994] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____1993 in
                         uu____1992 None FStar_Range.dummyRange in
                       let sort_range =
                         ((Prims.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b =
                         let uu____2001 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add the 'noeq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____2001 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b)
                  FStar_Syntax_Util.t_true dbs in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____2006 =
                       let uu____2007 =
                         let uu____2008 =
                           let uu____2009 =
                             let uu____2010 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs [((Prims.fst b), None)]
                               uu____2010 None in
                           FStar_Syntax_Syntax.as_arg uu____2009 in
                         [uu____2008] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____2007 in
                     uu____2006 None FStar_Range.dummyRange) dbs cond
          | uu____2027 -> FStar_Syntax_Util.t_true
let optimized_haseq_ty all_datas_in_the_bundle usubst us acc ty =
  let uu____2086 =
    match ty with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2098,bs,t,uu____2101,d_lids,uu____2103,uu____2104) ->
        (lid, bs, t, d_lids)
    | uu____2112 -> failwith "Impossible!" in
  match uu____2086 with
  | (lid,bs,t,d_lids) ->
      let bs = FStar_Syntax_Subst.subst_binders usubst bs in
      let t =
        let uu____2137 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst in
        FStar_Syntax_Subst.subst uu____2137 t in
      let uu____2144 = FStar_Syntax_Subst.open_term bs t in
      (match uu____2144 with
       | (bs,t) ->
           let ibs =
             let uu____2164 =
               let uu____2165 = FStar_Syntax_Subst.compress t in
               uu____2165.FStar_Syntax_Syntax.n in
             match uu____2164 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2172) -> ibs
             | uu____2183 -> [] in
           let ibs = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____2188 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____2189 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2188 uu____2189 in
           let ind =
             let uu____2194 =
               let uu____2195 =
                 FStar_List.map
                   (fun uu____2200  ->
                      match uu____2200 with
                      | (bv,aq) ->
                          let uu____2207 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2207, aq)) bs in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2195 in
             uu____2194 None FStar_Range.dummyRange in
           let ind =
             let uu____2215 =
               let uu____2216 =
                 FStar_List.map
                   (fun uu____2221  ->
                      match uu____2221 with
                      | (bv,aq) ->
                          let uu____2228 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2228, aq)) ibs in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2216 in
             uu____2215 None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____2236 =
               let uu____2237 =
                 let uu____2238 = FStar_Syntax_Syntax.as_arg ind in
                 [uu____2238] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2237 in
             uu____2236 None FStar_Range.dummyRange in
           let bs' =
             FStar_List.filter
               (fun b  ->
                  let uu____2252 = acc in
                  match uu____2252 with
                  | (uu____2260,en,uu____2262,uu____2263) ->
                      let opt =
                        let uu____2272 =
                          let uu____2273 = FStar_Syntax_Util.type_u () in
                          Prims.fst uu____2273 in
                        FStar_TypeChecker_Rel.try_subtype' en
                          (Prims.fst b).FStar_Syntax_Syntax.sort uu____2272
                          false in
                      (match opt with
                       | None  -> false
                       | Some uu____2276 -> true)) bs in
           let haseq_bs =
             FStar_List.fold_left
               (fun t  ->
                  fun b  ->
                    let uu____2280 =
                      let uu____2281 =
                        let uu____2282 =
                          let uu____2283 =
                            let uu____2284 =
                              FStar_Syntax_Syntax.bv_to_name (Prims.fst b) in
                            FStar_Syntax_Syntax.as_arg uu____2284 in
                          [uu____2283] in
                        FStar_Syntax_Syntax.mk_Tm_app
                          FStar_Syntax_Util.t_haseq uu____2282 in
                      uu____2281 None FStar_Range.dummyRange in
                    FStar_Syntax_Util.mk_conj t uu____2280)
               FStar_Syntax_Util.t_true bs' in
           let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
           let fml =
             let uu___83_2293 = fml in
             let uu____2294 =
               let uu____2295 =
                 let uu____2300 =
                   let uu____2301 =
                     let uu____2308 =
                       let uu____2310 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____2310] in
                     [uu____2308] in
                   FStar_Syntax_Syntax.Meta_pattern uu____2301 in
                 (fml, uu____2300) in
               FStar_Syntax_Syntax.Tm_meta uu____2295 in
             {
               FStar_Syntax_Syntax.n = uu____2294;
               FStar_Syntax_Syntax.tk = (uu___83_2293.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___83_2293.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___83_2293.FStar_Syntax_Syntax.vars)
             } in
           let fml =
             FStar_List.fold_right
               (fun b  ->
                  fun t  ->
                    let uu____2322 =
                      let uu____2323 =
                        let uu____2324 =
                          let uu____2325 =
                            let uu____2326 = FStar_Syntax_Subst.close [b] t in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2326 None in
                          FStar_Syntax_Syntax.as_arg uu____2325 in
                        [uu____2324] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2323 in
                    uu____2322 None FStar_Range.dummyRange) ibs fml in
           let fml =
             FStar_List.fold_right
               (fun b  ->
                  fun t  ->
                    let uu____2348 =
                      let uu____2349 =
                        let uu____2350 =
                          let uu____2351 =
                            let uu____2352 = FStar_Syntax_Subst.close [b] t in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2352 None in
                          FStar_Syntax_Syntax.as_arg uu____2351 in
                        [uu____2350] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2349 in
                    uu____2348 None FStar_Range.dummyRange) bs fml in
           let guard = FStar_Syntax_Util.mk_conj haseq_bs fml in
           let uu____2372 = acc in
           (match uu____2372 with
            | (l_axioms,env,guard',cond') ->
                let env = FStar_TypeChecker_Env.push_binders env bs in
                let env = FStar_TypeChecker_Env.push_binders env ibs in
                let t_datas =
                  FStar_List.filter
                    (fun s  ->
                       match s with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____2406,uu____2407,uu____2408,t_lid,uu____2410,uu____2411,uu____2412,uu____2413)
                           -> t_lid = lid
                       | uu____2418 -> failwith "Impossible")
                    all_datas_in_the_bundle in
                let cond =
                  FStar_List.fold_left
                    (fun acc  ->
                       fun d  ->
                         let uu____2422 =
                           optimized_haseq_soundness_for_data lid d usubst bs in
                         FStar_Syntax_Util.mk_conj acc uu____2422)
                    FStar_Syntax_Util.t_true t_datas in
                let axiom_lid =
                  FStar_Ident.lid_of_ids
                    (FStar_List.append lid.FStar_Ident.ns
                       [FStar_Ident.id_of_text
                          (Prims.strcat
                             (lid.FStar_Ident.ident).FStar_Ident.idText
                             "_haseq")]) in
                let uu____2424 = FStar_Syntax_Util.mk_conj guard' guard in
                let uu____2427 = FStar_Syntax_Util.mk_conj cond' cond in
                ((FStar_List.append l_axioms [(axiom_lid, fml)]), env,
                  uu____2424, uu____2427)))
let optimized_haseq_scheme:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t ->
          (FStar_TypeChecker_Env.env_t ->
             FStar_Ident.lident ->
               FStar_Syntax_Syntax.formula ->
                 FStar_Syntax_Syntax.qualifier Prims.list ->
                   FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
            -> FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun sig_bndle  ->
    fun tcs  ->
      fun datas  ->
        fun env0  ->
          fun tc_assume  ->
            let us =
              let ty = FStar_List.hd tcs in
              match ty with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (uu____2493,us,uu____2495,uu____2496,uu____2497,uu____2498,uu____2499,uu____2500)
                  -> us
              | uu____2507 -> failwith "Impossible!" in
            let uu____2508 = FStar_Syntax_Subst.univ_var_opening us in
            match uu____2508 with
            | (usubst,us) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env = FStar_TypeChecker_Env.push_univ_vars env us in
                  let uu____2524 =
                    FStar_List.fold_left (optimized_haseq_ty datas usubst us)
                      ([], env, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs in
                  match uu____2524 with
                  | (axioms,env,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond in
                      let uu____2556 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env phi in
                      (match uu____2556 with
                       | (phi,uu____2561) ->
                           ((let uu____2563 =
                               FStar_TypeChecker_Env.should_verify env in
                             if uu____2563
                             then
                               let uu____2564 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi) in
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 uu____2564
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____2572  ->
                                      match uu____2572 with
                                      | (lid,fml) ->
                                          let se =
                                            tc_assume env lid fml []
                                              FStar_Range.dummyRange in
                                          FStar_List.append l [se]) [] axioms in
                             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                               "haseq";
                             ses)))))
let unoptimized_haseq_data:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lident Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                FStar_Syntax_Syntax.syntax
  =
  fun usubst  ->
    fun bs  ->
      fun haseq_ind  ->
        fun mutuals  ->
          fun acc  ->
            fun data  ->
              let rec is_mutual t =
                let uu____2615 =
                  let uu____2616 = FStar_Syntax_Subst.compress t in
                  uu____2616.FStar_Syntax_Syntax.n in
                match uu____2615 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____2626) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____2653 = is_mutual t' in
                    if uu____2653
                    then true
                    else
                      (let uu____2655 = FStar_List.map Prims.fst args in
                       exists_mutual uu____2655)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____2668) -> is_mutual t'
                | uu____2673 -> false
              and exists_mutual uu___79_2674 =
                match uu___79_2674 with
                | [] -> false
                | hd::tl -> (is_mutual hd) || (exists_mutual tl) in
              let dt = datacon_typ data in
              let dt = FStar_Syntax_Subst.subst usubst dt in
              let uu____2691 =
                let uu____2692 = FStar_Syntax_Subst.compress dt in
                uu____2692.FStar_Syntax_Syntax.n in
              match uu____2691 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2698) ->
                  let dbs =
                    let uu____2713 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    Prims.snd uu____2713 in
                  let dbs =
                    let uu____2735 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____2735 dbs in
                  let dbs = FStar_Syntax_Subst.open_binders dbs in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort = (Prims.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____2747 =
                               let uu____2748 =
                                 let uu____2749 =
                                   FStar_Syntax_Syntax.as_arg
                                     (Prims.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____2749] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____2748 in
                             uu____2747 None FStar_Range.dummyRange in
                           let haseq_sort =
                             let uu____2755 = is_mutual sort in
                             if uu____2755
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort)
                      FStar_Syntax_Util.t_true dbs in
                  let cond =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____2762 =
                             let uu____2763 =
                               let uu____2764 =
                                 let uu____2765 =
                                   let uu____2766 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((Prims.fst b), None)] uu____2766 None in
                                 FStar_Syntax_Syntax.as_arg uu____2765 in
                               [uu____2764] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____2763 in
                           uu____2762 None FStar_Range.dummyRange) dbs cond in
                  FStar_Syntax_Util.mk_conj acc cond
              | uu____2783 -> acc
let unoptimized_haseq_ty all_datas_in_the_bundle mutuals usubst us acc ty =
  let uu____2826 =
    match ty with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2838,bs,t,uu____2841,d_lids,uu____2843,uu____2844) ->
        (lid, bs, t, d_lids)
    | uu____2852 -> failwith "Impossible!" in
  match uu____2826 with
  | (lid,bs,t,d_lids) ->
      let bs = FStar_Syntax_Subst.subst_binders usubst bs in
      let t =
        let uu____2868 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst in
        FStar_Syntax_Subst.subst uu____2868 t in
      let uu____2875 = FStar_Syntax_Subst.open_term bs t in
      (match uu____2875 with
       | (bs,t) ->
           let ibs =
             let uu____2886 =
               let uu____2887 = FStar_Syntax_Subst.compress t in
               uu____2887.FStar_Syntax_Syntax.n in
             match uu____2886 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2894) -> ibs
             | uu____2905 -> [] in
           let ibs = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____2910 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____2911 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2910 uu____2911 in
           let ind =
             let uu____2916 =
               let uu____2917 =
                 FStar_List.map
                   (fun uu____2922  ->
                      match uu____2922 with
                      | (bv,aq) ->
                          let uu____2929 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2929, aq)) bs in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2917 in
             uu____2916 None FStar_Range.dummyRange in
           let ind =
             let uu____2937 =
               let uu____2938 =
                 FStar_List.map
                   (fun uu____2943  ->
                      match uu____2943 with
                      | (bv,aq) ->
                          let uu____2950 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2950, aq)) ibs in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2938 in
             uu____2937 None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____2958 =
               let uu____2959 =
                 let uu____2960 = FStar_Syntax_Syntax.as_arg ind in
                 [uu____2960] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2959 in
             uu____2958 None FStar_Range.dummyRange in
           let t_datas =
             FStar_List.filter
               (fun s  ->
                  match s with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____2968,uu____2969,uu____2970,t_lid,uu____2972,uu____2973,uu____2974,uu____2975)
                      -> t_lid = lid
                  | uu____2980 -> failwith "Impossible")
               all_datas_in_the_bundle in
           let data_cond =
             FStar_List.fold_left
               (unoptimized_haseq_data usubst bs haseq_ind mutuals)
               FStar_Syntax_Util.t_true t_datas in
           let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
           let fml =
             let uu___84_2986 = fml in
             let uu____2987 =
               let uu____2988 =
                 let uu____2993 =
                   let uu____2994 =
                     let uu____3001 =
                       let uu____3003 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____3003] in
                     [uu____3001] in
                   FStar_Syntax_Syntax.Meta_pattern uu____2994 in
                 (fml, uu____2993) in
               FStar_Syntax_Syntax.Tm_meta uu____2988 in
             {
               FStar_Syntax_Syntax.n = uu____2987;
               FStar_Syntax_Syntax.tk = (uu___84_2986.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___84_2986.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___84_2986.FStar_Syntax_Syntax.vars)
             } in
           let fml =
             FStar_List.fold_right
               (fun b  ->
                  fun t  ->
                    let uu____3015 =
                      let uu____3016 =
                        let uu____3017 =
                          let uu____3018 =
                            let uu____3019 = FStar_Syntax_Subst.close [b] t in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____3019 None in
                          FStar_Syntax_Syntax.as_arg uu____3018 in
                        [uu____3017] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3016 in
                    uu____3015 None FStar_Range.dummyRange) ibs fml in
           let fml =
             FStar_List.fold_right
               (fun b  ->
                  fun t  ->
                    let uu____3041 =
                      let uu____3042 =
                        let uu____3043 =
                          let uu____3044 =
                            let uu____3045 = FStar_Syntax_Subst.close [b] t in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____3045 None in
                          FStar_Syntax_Syntax.as_arg uu____3044 in
                        [uu____3043] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3042 in
                    uu____3041 None FStar_Range.dummyRange) bs fml in
           FStar_Syntax_Util.mk_conj acc fml)
let unoptimized_haseq_scheme:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t ->
          (FStar_TypeChecker_Env.env_t ->
             FStar_Ident.lident ->
               FStar_Syntax_Syntax.formula ->
                 FStar_Syntax_Syntax.qualifier Prims.list ->
                   FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
            -> FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun sig_bndle  ->
    fun tcs  ->
      fun datas  ->
        fun env0  ->
          fun tc_assume  ->
            let mutuals =
              FStar_List.map
                (fun ty  ->
                   match ty with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (lid,uu____3114,uu____3115,uu____3116,uu____3117,uu____3118,uu____3119,uu____3120)
                       -> lid
                   | uu____3127 -> failwith "Impossible!") tcs in
            let uu____3128 =
              let ty = FStar_List.hd tcs in
              match ty with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____3136,uu____3137,uu____3138,uu____3139,uu____3140,uu____3141)
                  -> (lid, us)
              | uu____3148 -> failwith "Impossible!" in
            match uu____3128 with
            | (lid,us) ->
                let uu____3154 = FStar_Syntax_Subst.univ_var_opening us in
                (match uu____3154 with
                 | (usubst,us) ->
                     let fml =
                       FStar_List.fold_left
                         (unoptimized_haseq_ty datas mutuals usubst us)
                         FStar_Syntax_Util.t_true tcs in
                     let env =
                       FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                     ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                        "haseq";
                      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                        env sig_bndle;
                      (let env = FStar_TypeChecker_Env.push_univ_vars env us in
                       let se =
                         let uu____3172 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")]) in
                         tc_assume env uu____3172 fml []
                           FStar_Range.dummyRange in
                       (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                         "haseq";
                       [se])))
let check_inductive_well_typedness:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt* FStar_Syntax_Syntax.sigelt Prims.list*
            FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let uu____3202 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___80_3212  ->
                    match uu___80_3212 with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____3213 ->
                        true
                    | uu____3225 -> false)) in
          match uu____3202 with
          | (tys,datas) ->
              ((let uu____3238 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___81_3240  ->
                          match uu___81_3240 with
                          | FStar_Syntax_Syntax.Sig_datacon uu____3241 ->
                              false
                          | uu____3252 -> true)) in
                if uu____3238
                then
                  let uu____3253 =
                    let uu____3254 =
                      let uu____3257 = FStar_TypeChecker_Env.get_range env in
                      ("Mutually defined type contains a non-inductive element",
                        uu____3257) in
                    FStar_Errors.Error uu____3254 in
                  Prims.raise uu____3253
                else ());
               (let env0 = env in
                let uu____3260 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____3274  ->
                         match uu____3274 with
                         | (env,all_tcs,g) ->
                             let uu____3296 = tc_tycon env tc in
                             (match uu____3296 with
                              | (env,tc,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____3313 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Low in
                                    if uu____3313
                                    then
                                      let uu____3314 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____3314
                                    else ());
                                   (let uu____3316 =
                                      let uu____3317 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____3317 in
                                    (env, ((tc, tc_u) :: all_tcs),
                                      uu____3316))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard) in
                match uu____3260 with
                | (env,tcs,g) ->
                    let uu____3342 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____3350  ->
                             match uu____3350 with
                             | (datas,g) ->
                                 let uu____3361 =
                                   let uu____3364 = tc_data env tcs in
                                   uu____3364 se in
                                 (match uu____3361 with
                                  | (data,g') ->
                                      let uu____3374 =
                                        FStar_TypeChecker_Rel.conj_guard g g' in
                                      ((data :: datas), uu____3374))) datas
                        ([], g) in
                    (match uu____3342 with
                     | (datas,g) ->
                         let uu____3386 =
                           generalize_and_inst_within env0 g tcs datas in
                         (match uu____3386 with
                          | (tcs,datas) ->
                              let sig_bndle =
                                let uu____3403 =
                                  let uu____3411 =
                                    FStar_TypeChecker_Env.get_range env0 in
                                  ((FStar_List.append tcs datas), quals,
                                    lids, uu____3411) in
                                FStar_Syntax_Syntax.Sig_bundle uu____3403 in
                              (sig_bndle, tcs, datas)))))