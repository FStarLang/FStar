open Prims
let tc_tycon :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_TypeChecker_Env.env_t * FStar_Syntax_Syntax.sigelt *
        FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (tc,uvs,tps,k,mutuals,data,quals,r) ->
          let uu____34 = FStar_Syntax_Subst.open_term tps k  in
          (match uu____34 with
           | (tps1,k1) ->
               let uu____43 = FStar_TypeChecker_TcTerm.tc_binders env tps1
                  in
               (match uu____43 with
                | (tps2,env_tps,guard_params,us) ->
                    let uu____56 =
                      FStar_TypeChecker_Util.arrow_formals env k1  in
                    (match uu____56 with
                     | (indices,t) ->
                         let uu____65 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices
                            in
                         (match uu____65 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____78 =
                                let uu____81 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t
                                   in
                                match uu____81 with
                                | (t1,uu____88,g) ->
                                    let uu____90 =
                                      let uu____91 =
                                        let uu____92 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g
                                           in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____92
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____91
                                       in
                                    (t1, uu____90)
                                 in
                              (match uu____78 with
                               | (t1,guard) ->
                                   let k2 =
                                     let uu____100 =
                                       FStar_Syntax_Syntax.mk_Total t1  in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____100
                                      in
                                   let uu____101 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____101 with
                                    | (t_type,u) ->
                                        ((let uu____111 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type
                                             in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____111);
                                         (let t_tc =
                                            let uu____113 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____113
                                             in
                                          let tps3 =
                                            FStar_Syntax_Subst.close_binders
                                              tps2
                                             in
                                          let k3 =
                                            FStar_Syntax_Subst.close tps3 k2
                                             in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              None
                                             in
                                          let uu____119 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc)
                                             in
                                          (uu____119,
                                            (FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc, [], tps3, k3, mutuals,
                                                 data, quals, r)), u, guard)))))))))
      | uu____125 -> failwith "impossible"
  
let tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun tcs  ->
      fun uu___77_150  ->
        match uu___77_150 with
        | FStar_Syntax_Syntax.Sig_datacon
            (c,_uvs,t,tc_lid,ntps,quals,_mutual_tcs,r) ->
            let uu____166 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____180  ->
                     match uu____180 with
                     | (se,u_tc) ->
                         let uu____189 =
                           let uu____190 =
                             let uu____191 =
                               FStar_Syntax_Util.lid_of_sigelt se  in
                             FStar_Util.must uu____191  in
                           FStar_Ident.lid_equals tc_lid uu____190  in
                         if uu____189
                         then
                           (match se with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____201,uu____202,tps,uu____204,uu____205,uu____206,uu____207,uu____208)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____229  ->
                                          match uu____229 with
                                          | (x,uu____236) ->
                                              (x,
                                                (Some
                                                   FStar_Syntax_Syntax.imp_tag))))
                                   in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1  in
                                let uu____239 =
                                  let uu____243 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2
                                     in
                                  (uu____243, tps2, u_tc)  in
                                Some uu____239
                            | uu____247 -> failwith "Impossible")
                         else None)
                 in
              match tps_u_opt with
              | Some x -> x
              | None  ->
                  if FStar_Ident.lid_equals tc_lid FStar_Syntax_Const.exn_lid
                  then (env, [], FStar_Syntax_Syntax.U_zero)
                  else
                    Prims.raise
                      (FStar_Errors.Error ("Unexpected data constructor", r))
               in
            (match uu____166 with
             | (env1,tps,u_tc) ->
                 let uu____286 =
                   let uu____289 =
                     let uu____290 = FStar_Syntax_Subst.compress t  in
                     uu____290.FStar_Syntax_Syntax.n  in
                   match uu____289 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____307 = FStar_Util.first_N ntps bs  in
                       (match uu____307 with
                        | (uu____320,bs') ->
                            let t1 =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_arrow (bs', res)))
                                None t.FStar_Syntax_Syntax.pos
                               in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____356  ->
                                        match uu____356 with
                                        | (x,uu____360) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x)))
                               in
                            let uu____361 =
                              FStar_Syntax_Subst.subst subst1 t1  in
                            FStar_TypeChecker_Util.arrow_formals env1
                              uu____361)
                   | uu____362 -> ([], t)  in
                 (match uu____286 with
                  | (arguments,result) ->
                      ((let uu____373 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low
                           in
                        if uu____373
                        then
                          let uu____374 = FStar_Syntax_Print.lid_to_string c
                             in
                          let uu____375 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments
                             in
                          let uu____376 =
                            FStar_Syntax_Print.term_to_string result  in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____374
                            uu____375 uu____376
                        else ());
                       (let uu____378 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments
                           in
                        match uu____378 with
                        | (arguments1,env',us) ->
                            let uu____387 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result
                               in
                            (match uu____387 with
                             | (result1,res_lcomp) ->
                                 ((let uu____395 =
                                     let uu____396 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.lcomp_res_typ
                                        in
                                     uu____396.FStar_Syntax_Syntax.n  in
                                   match uu____395 with
                                   | FStar_Syntax_Syntax.Tm_type uu____399 ->
                                       ()
                                   | ty ->
                                       let uu____401 =
                                         let uu____402 =
                                           let uu____405 =
                                             let uu____406 =
                                               FStar_Syntax_Print.term_to_string
                                                 result1
                                                in
                                             let uu____407 =
                                               FStar_Syntax_Print.term_to_string
                                                 res_lcomp.FStar_Syntax_Syntax.lcomp_res_typ
                                                in
                                             FStar_Util.format2
                                               "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                               uu____406 uu____407
                                              in
                                           (uu____405, r)  in
                                         FStar_Errors.Error uu____402  in
                                       Prims.raise uu____401);
                                  (let uu____408 =
                                     FStar_Syntax_Util.head_and_args result1
                                      in
                                   match uu____408 with
                                   | (head1,uu____421) ->
                                       ((let uu____437 =
                                           let uu____438 =
                                             FStar_Syntax_Subst.compress
                                               head1
                                              in
                                           uu____438.FStar_Syntax_Syntax.n
                                            in
                                         match uu____437 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____442 ->
                                             let uu____443 =
                                               let uu____444 =
                                                 let uu____447 =
                                                   let uu____448 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       tc_lid
                                                      in
                                                   let uu____449 =
                                                     FStar_Syntax_Print.term_to_string
                                                       head1
                                                      in
                                                   FStar_Util.format2
                                                     "Expected a constructor of type %s; got %s"
                                                     uu____448 uu____449
                                                    in
                                                 (uu____447, r)  in
                                               FStar_Errors.Error uu____444
                                                in
                                             Prims.raise uu____443);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____454  ->
                                                  fun u_x  ->
                                                    match uu____454 with
                                                    | (x,uu____459) ->
                                                        let uu____460 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc
                                                           in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____460)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us
                                            in
                                         let t1 =
                                           let uu____462 =
                                             let uu____463 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____477  ->
                                                       match uu____477 with
                                                       | (x,uu____484) ->
                                                           (x,
                                                             (Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true)))))
                                                in
                                             FStar_List.append uu____463
                                               arguments1
                                              in
                                           let uu____489 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1
                                              in
                                           FStar_Syntax_Util.arrow uu____462
                                             uu____489
                                            in
                                         ((FStar_Syntax_Syntax.Sig_datacon
                                             (c, [], t1, tc_lid, ntps, quals,
                                               [], r)), g))))))))))
        | uu____493 -> failwith "impossible"
  
let generalize_and_inst_within :
  FStar_TypeChecker_Env.env_t ->
    FStar_TypeChecker_Env.guard_t ->
      (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list
        ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
            Prims.list)
  =
  fun env  ->
    fun g  ->
      fun tcs  ->
        fun datas  ->
          let tc_universe_vars = FStar_List.map Prims.snd tcs  in
          let g1 =
            let uu___83_529 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___83_529.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___83_529.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (Prims.snd g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___83_529.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____535 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____535
           then
             let uu____536 = FStar_TypeChecker_Rel.guard_to_string env g1  in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____536
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____547  ->
                     match uu____547 with
                     | (se,uu____551) ->
                         (match se with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____552,uu____553,tps,k,uu____556,uu____557,uu____558,uu____559)
                              ->
                              let uu____566 =
                                let uu____567 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____567
                                 in
                              FStar_Syntax_Syntax.null_binder uu____566
                          | uu____568 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun uu___78_573  ->
                     match uu___78_573 with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____574,uu____575,t,uu____577,uu____578,uu____579,uu____580,uu____581)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____586 -> failwith "Impossible"))
              in
           let t =
             let uu____588 =
               FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit
                in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____588
              in
           (let uu____590 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____590
            then
              let uu____591 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____591
            else ());
           (let uu____593 = FStar_TypeChecker_Util.generalize_universes env t
               in
            match uu____593 with
            | (uvs,t1) ->
                ((let uu____603 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____603
                  then
                    let uu____604 =
                      let uu____605 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____605
                        (FStar_String.concat ", ")
                       in
                    let uu____611 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____604 uu____611
                  else ());
                 (let uu____613 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____613 with
                  | (uvs1,t2) ->
                      let uu____622 =
                        FStar_TypeChecker_Util.arrow_formals env t2  in
                      (match uu____622 with
                       | (args,uu____630) ->
                           let uu____631 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____631 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____668  ->
                                       fun uu____669  ->
                                         match (uu____668, uu____669) with
                                         | ((x,uu____679),(se,uu____681)) ->
                                             (match se with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____687,tps,uu____689,mutuals,datas1,quals,r)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____701 =
                                                    let uu____707 =
                                                      let uu____708 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____708.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____707 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____728 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____728 with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_TypeChecker_Env.result_typ
                                                                    env c
                                                               | uu____765 ->
                                                                   let uu____769
                                                                    =
                                                                    FStar_ST.read
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk
                                                                     in
                                                                   (FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c)))
                                                                    uu____769
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____790 -> ([], ty)
                                                     in
                                                  (match uu____701 with
                                                   | (tps1,t3) ->
                                                       FStar_Syntax_Syntax.Sig_inductive_typ
                                                         (tc, uvs1, tps1, t3,
                                                           mutuals, datas1,
                                                           quals, r))
                                              | uu____810 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____814 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_28  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_28))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___79_831  ->
                                                match uu___79_831 with
                                                | FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc,uu____836,uu____837,uu____838,uu____839,uu____840,uu____841,uu____842)
                                                    -> (tc, uvs_universes)
                                                | uu____850 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____856  ->
                                           fun d  ->
                                             match uu____856 with
                                             | (t3,uu____861) ->
                                                 (match d with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____863,uu____864,tc,ntps,quals,mutuals,r)
                                                      ->
                                                      let ty =
                                                        let uu____875 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____875
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      FStar_Syntax_Syntax.Sig_datacon
                                                        (l, uvs1, ty, tc,
                                                          ntps, quals,
                                                          mutuals, r)
                                                  | uu____878 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____887 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____887
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____895 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____895
  
let try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes)
  =
  fun t  ->
    let uu____904 =
      let uu____905 = FStar_Syntax_Subst.compress t  in
      uu____905.FStar_Syntax_Syntax.n  in
    match uu____904 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____921 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____924 -> failwith "Node is not an fvar or a Tm_uinst"
  
type unfolded_memo_elt =
  (FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list
type unfolded_memo_t = unfolded_memo_elt FStar_ST.ref
let already_unfolded :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ilid  ->
    fun arrghs  ->
      fun unfolded  ->
        fun env  ->
          let uu____943 = FStar_ST.read unfolded  in
          FStar_List.existsML
            (fun uu____955  ->
               match uu____955 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____975 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        Prims.fst uu____975  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (Prims.fst a) (Prims.fst a'))) true args
                        l)) uu____943
  
let rec ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1070 =
             let uu____1071 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____1071
              in
           debug_log env uu____1070);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype
              in
           (let uu____1074 =
              let uu____1075 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1075
               in
            debug_log env uu____1074);
           (let uu____1076 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____1076) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1078 =
                  let uu____1079 = FStar_Syntax_Subst.compress btype1  in
                  uu____1079.FStar_Syntax_Syntax.n  in
                match uu____1078 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1098 = try_get_fv t  in
                    (match uu____1098 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1110  ->
                                 match uu____1110 with
                                 | (t1,uu____1114) ->
                                     let uu____1115 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____1115) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____1135 =
                        let uu____1136 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        Prims.op_Negation uu____1136  in
                      if uu____1135
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking strict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____1142  ->
                               match uu____1142 with
                               | (b,uu____1146) ->
                                   let uu____1147 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____1147) sbs)
                           &&
                           ((let uu____1148 =
                               let uu____1151 =
                                 FStar_TypeChecker_Env.result_typ env c  in
                               FStar_Syntax_Subst.open_term sbs uu____1151
                                in
                             match uu____1148 with
                             | (uu____1152,return_type) ->
                                 let uu____1154 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____1154)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____1155 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____1157 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____1160) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____1167) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____1173,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____1208  ->
                          match uu____1208 with
                          | (p,uu____1216,t) ->
                              let bs =
                                let uu____1226 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____1226
                                 in
                              let uu____1228 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____1228 with
                               | (bs1,t1) ->
                                   let uu____1233 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____1233)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1235,uu____1236)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____1256 ->
                    ((let uu____1258 =
                        let uu____1259 =
                          let uu____1260 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____1261 =
                            let uu____1262 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____1262  in
                          Prims.strcat uu____1260 uu____1261  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____1259
                         in
                      debug_log env uu____1258);
                     false)))))

and ty_nested_positive_in_inductive :
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
              (let uu____1270 =
                 let uu____1271 =
                   let uu____1272 =
                     let uu____1273 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____1273  in
                   Prims.strcat ilid.FStar_Ident.str uu____1272  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____1271
                  in
               debug_log env uu____1270);
              (let uu____1274 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____1274 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____1284 =
                        already_unfolded ilid args unfolded env  in
                      if uu____1284
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid
                            in
                         (let uu____1289 =
                            let uu____1290 =
                              let uu____1291 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____1291
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____1290
                             in
                          debug_log env uu____1289);
                         (let uu____1293 =
                            let uu____1294 = FStar_ST.read unfolded  in
                            let uu____1298 =
                              let uu____1302 =
                                let uu____1310 =
                                  let uu____1316 =
                                    FStar_List.splitAt num_ibs args  in
                                  Prims.fst uu____1316  in
                                (ilid, uu____1310)  in
                              [uu____1302]  in
                            FStar_List.append uu____1294 uu____1298  in
                          FStar_ST.write unfolded uu____1293);
                         FStar_List.for_all
                           (fun d  ->
                              ty_nested_positive_in_dlid ty_lid d ilid us
                                args num_ibs unfolded env) idatas)))

and ty_nested_positive_in_dlid :
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
                  (let uu____1374 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____1374 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Unionfind.change u'' (Some u)
                               | uu____1386 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us;
                        (let dt1 =
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
                         (let uu____1389 =
                            let uu____1390 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____1390
                             in
                          debug_log env uu____1389);
                         (let uu____1391 =
                            let uu____1392 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____1392.FStar_Syntax_Syntax.n  in
                          match uu____1391 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____1408 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____1408 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____1435 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____1435 dbs1
                                       in
                                    let c1 =
                                      let uu____1438 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____1438 c
                                       in
                                    let uu____1440 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____1440 with
                                     | (args1,uu____1458) ->
                                         let subst1 =
                                           FStar_List.fold_left2
                                             (fun subst1  ->
                                                fun ib  ->
                                                  fun arg  ->
                                                    FStar_List.append subst1
                                                      [FStar_Syntax_Syntax.NT
                                                         ((Prims.fst ib),
                                                           (Prims.fst arg))])
                                             [] ibs1 args1
                                            in
                                         let dbs3 =
                                           FStar_Syntax_Subst.subst_binders
                                             subst1 dbs2
                                            in
                                         let c2 =
                                           let uu____1504 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____1504 c1
                                            in
                                         ((let uu____1512 =
                                             let uu____1513 =
                                               let uu____1514 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____1515 =
                                                 let uu____1516 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____1516
                                                  in
                                               Prims.strcat uu____1514
                                                 uu____1515
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____1513
                                              in
                                           debug_log env uu____1512);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____1517 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____1519 =
                                  let uu____1520 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____1520.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____1519
                                  ilid num_ibs unfolded env))))))

and ty_nested_positive_in_type :
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
              | FStar_Syntax_Syntax.Tm_app (t1,args) ->
                  (debug_log env
                     "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself";
                   (let uu____1546 = try_get_fv t1  in
                    match uu____1546 with
                    | (fv,uu____1550) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____1569 =
                      let uu____1570 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____1570
                       in
                    debug_log env uu____1569);
                   (let uu____1571 =
                      FStar_List.fold_left
                        (fun uu____1578  ->
                           fun b  ->
                             match uu____1578 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____1591 =
                                      ty_strictly_positive_in_type ty_lid
                                        (Prims.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____1592 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____1591, uu____1592))) (true, env)
                        sbs
                       in
                    match uu____1571 with | (b,uu____1598) -> b))
              | uu____1599 ->
                  failwith "Nested positive check, unhandled case"

let ty_positive_in_datacon :
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
              let uu____1618 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____1618 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Unionfind.change u'' (Some u)
                          | uu____1630 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____1632 =
                      let uu____1633 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____1633
                       in
                    debug_log env uu____1632);
                   (let uu____1634 =
                      let uu____1635 = FStar_Syntax_Subst.compress dt  in
                      uu____1635.FStar_Syntax_Syntax.n  in
                    match uu____1634 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____1638 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1641) ->
                        let dbs1 =
                          let uu____1656 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          Prims.snd uu____1656  in
                        let dbs2 =
                          let uu____1678 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____1678 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____1682 =
                            let uu____1683 =
                              let uu____1684 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____1684 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____1683
                             in
                          debug_log env uu____1682);
                         (let uu____1690 =
                            FStar_List.fold_left
                              (fun uu____1697  ->
                                 fun b  ->
                                   match uu____1697 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____1710 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (Prims.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____1711 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____1710, uu____1711)))
                              (true, env) dbs3
                             in
                          match uu____1690 with | (b,uu____1717) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____1718,uu____1719) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | uu____1735 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env_t -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____1753 =
        match ty with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____1763,uu____1764,uu____1765,uu____1766,uu____1767)
            -> (lid, us, bs)
        | uu____1774 -> failwith "Impossible!"  in
      match uu____1753 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____1781 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____1781 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____1796 =
                 let uu____1798 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 Prims.snd uu____1798  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____1804 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____1804
                      unfolded_inductives env2) uu____1796)
  
let datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1811,uu____1812,t,uu____1814,uu____1815,uu____1816,uu____1817,uu____1818)
        -> t
    | uu____1823 -> failwith "Impossible!"
  
let optimized_haseq_soundness_for_data :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term
  =
  fun ty_lid  ->
    fun data  ->
      fun usubst  ->
        fun bs  ->
          let dt = datacon_typ data  in
          let dt1 = FStar_Syntax_Subst.subst usubst dt  in
          let uu____1840 =
            let uu____1841 = FStar_Syntax_Subst.compress dt1  in
            uu____1841.FStar_Syntax_Syntax.n  in
          match uu____1840 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1845) ->
              let dbs1 =
                let uu____1860 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                Prims.snd uu____1860  in
              let dbs2 =
                let uu____1882 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____1882 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____1891 =
                           let uu____1892 =
                             let uu____1893 =
                               FStar_Syntax_Syntax.as_arg
                                 (Prims.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____1893]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____1892
                            in
                         uu____1891 None FStar_Range.dummyRange  in
                       let sort_range =
                         ((Prims.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____1900 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add the 'noeq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____1900 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____1905 =
                       let uu____1906 =
                         let uu____1907 =
                           let uu____1908 =
                             let uu____1909 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs [((Prims.fst b), None)]
                               uu____1909 None
                              in
                           FStar_Syntax_Syntax.as_arg uu____1908  in
                         [uu____1907]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____1906
                        in
                     uu____1905 None FStar_Range.dummyRange) dbs3 cond
          | uu____1926 -> FStar_Syntax_Util.t_true
  
let optimized_haseq_ty all_datas_in_the_bundle usubst us acc ty =
  let uu____1985 =
    match ty with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____1997,bs,t,uu____2000,d_lids,uu____2002,uu____2003) ->
        (lid, bs, t, d_lids)
    | uu____2011 -> failwith "Impossible!"  in
  match uu____1985 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
      let t1 =
        let uu____2036 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst  in
        FStar_Syntax_Subst.subst uu____2036 t  in
      let uu____2043 = FStar_Syntax_Subst.open_term bs1 t1  in
      (match uu____2043 with
       | (bs2,t2) ->
           let ibs =
             let uu____2063 =
               let uu____2064 = FStar_Syntax_Subst.compress t2  in
               uu____2064.FStar_Syntax_Syntax.n  in
             match uu____2063 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2071) -> ibs
             | uu____2082 -> []  in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
           let ind =
             let uu____2087 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____2088 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us  in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2087 uu____2088  in
           let ind1 =
             let uu____2093 =
               let uu____2094 =
                 FStar_List.map
                   (fun uu____2099  ->
                      match uu____2099 with
                      | (bv,aq) ->
                          let uu____2106 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2106, aq)) bs2
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2094  in
             uu____2093 None FStar_Range.dummyRange  in
           let ind2 =
             let uu____2114 =
               let uu____2115 =
                 FStar_List.map
                   (fun uu____2120  ->
                      match uu____2120 with
                      | (bv,aq) ->
                          let uu____2127 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2127, aq)) ibs1
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2115  in
             uu____2114 None FStar_Range.dummyRange  in
           let haseq_ind =
             let uu____2135 =
               let uu____2136 =
                 let uu____2137 = FStar_Syntax_Syntax.as_arg ind2  in
                 [uu____2137]  in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2136
                in
             uu____2135 None FStar_Range.dummyRange  in
           let bs' =
             FStar_List.filter
               (fun b  ->
                  let uu____2151 = acc  in
                  match uu____2151 with
                  | (uu____2159,en,uu____2161,uu____2162) ->
                      let opt =
                        let uu____2171 =
                          let uu____2172 = FStar_Syntax_Util.type_u ()  in
                          Prims.fst uu____2172  in
                        FStar_TypeChecker_Rel.try_subtype' en
                          (Prims.fst b).FStar_Syntax_Syntax.sort uu____2171
                          false
                         in
                      (match opt with
                       | None  -> false
                       | Some uu____2175 -> true)) bs2
              in
           let haseq_bs =
             FStar_List.fold_left
               (fun t3  ->
                  fun b  ->
                    let uu____2179 =
                      let uu____2180 =
                        let uu____2181 =
                          let uu____2182 =
                            let uu____2183 =
                              FStar_Syntax_Syntax.bv_to_name (Prims.fst b)
                               in
                            FStar_Syntax_Syntax.as_arg uu____2183  in
                          [uu____2182]  in
                        FStar_Syntax_Syntax.mk_Tm_app
                          FStar_Syntax_Util.t_haseq uu____2181
                         in
                      uu____2180 None FStar_Range.dummyRange  in
                    FStar_Syntax_Util.mk_conj t3 uu____2179)
               FStar_Syntax_Util.t_true bs'
              in
           let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
           let fml1 =
             let uu___84_2192 = fml  in
             let uu____2193 =
               let uu____2194 =
                 let uu____2199 =
                   let uu____2200 =
                     let uu____2207 =
                       let uu____2209 = FStar_Syntax_Syntax.as_arg haseq_ind
                          in
                       [uu____2209]  in
                     [uu____2207]  in
                   FStar_Syntax_Syntax.Meta_pattern uu____2200  in
                 (fml, uu____2199)  in
               FStar_Syntax_Syntax.Tm_meta uu____2194  in
             {
               FStar_Syntax_Syntax.n = uu____2193;
               FStar_Syntax_Syntax.tk = (uu___84_2192.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___84_2192.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___84_2192.FStar_Syntax_Syntax.vars)
             }  in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2221 =
                      let uu____2222 =
                        let uu____2223 =
                          let uu____2224 =
                            let uu____2225 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2225 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2224  in
                        [uu____2223]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2222
                       in
                    uu____2221 None FStar_Range.dummyRange) ibs1 fml1
              in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2247 =
                      let uu____2248 =
                        let uu____2249 =
                          let uu____2250 =
                            let uu____2251 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2251 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2250  in
                        [uu____2249]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2248
                       in
                    uu____2247 None FStar_Range.dummyRange) bs2 fml2
              in
           let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3  in
           let uu____2271 = acc  in
           (match uu____2271 with
            | (l_axioms,env,guard',cond') ->
                let env1 = FStar_TypeChecker_Env.push_binders env bs2  in
                let env2 = FStar_TypeChecker_Env.push_binders env1 ibs1  in
                let t_datas =
                  FStar_List.filter
                    (fun s  ->
                       match s with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____2305,uu____2306,uu____2307,t_lid,uu____2309,uu____2310,uu____2311,uu____2312)
                           -> t_lid = lid
                       | uu____2317 -> failwith "Impossible")
                    all_datas_in_the_bundle
                   in
                let cond =
                  FStar_List.fold_left
                    (fun acc1  ->
                       fun d  ->
                         let uu____2321 =
                           optimized_haseq_soundness_for_data lid d usubst
                             bs2
                            in
                         FStar_Syntax_Util.mk_conj acc1 uu____2321)
                    FStar_Syntax_Util.t_true t_datas
                   in
                let axiom_lid =
                  FStar_Ident.lid_of_ids
                    (FStar_List.append lid.FStar_Ident.ns
                       [FStar_Ident.id_of_text
                          (Prims.strcat
                             (lid.FStar_Ident.ident).FStar_Ident.idText
                             "_haseq")])
                   in
                let uu____2323 = FStar_Syntax_Util.mk_conj guard' guard  in
                let uu____2326 = FStar_Syntax_Util.mk_conj cond' cond  in
                ((FStar_List.append l_axioms [(axiom_lid, fml3)]), env2,
                  uu____2323, uu____2326)))
  
let optimized_haseq_scheme :
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
              let ty = FStar_List.hd tcs  in
              match ty with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (uu____2392,us,uu____2394,uu____2395,uu____2396,uu____2397,uu____2398,uu____2399)
                  -> us
              | uu____2406 -> failwith "Impossible!"  in
            let uu____2407 = FStar_Syntax_Subst.univ_var_opening us  in
            match uu____2407 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                   in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                  let uu____2423 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs
                     in
                  match uu____2423 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond  in
                      let uu____2455 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                         in
                      (match uu____2455 with
                       | (phi1,uu____2460) ->
                           ((let uu____2462 =
                               FStar_TypeChecker_Env.should_verify env2  in
                             if uu____2462
                             then
                               let uu____2463 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1)
                                  in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____2463
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____2471  ->
                                      match uu____2471 with
                                      | (lid,fml) ->
                                          let se =
                                            tc_assume env2 lid fml []
                                              FStar_Range.dummyRange
                                             in
                                          FStar_List.append l [se]) [] axioms
                                in
                             (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                               "haseq";
                             ses)))))
  
let unoptimized_haseq_data :
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
                let uu____2514 =
                  let uu____2515 = FStar_Syntax_Subst.compress t  in
                  uu____2515.FStar_Syntax_Syntax.n  in
                match uu____2514 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____2525) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____2552 = is_mutual t'  in
                    if uu____2552
                    then true
                    else
                      (let uu____2554 = FStar_List.map Prims.fst args  in
                       exists_mutual uu____2554)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____2567) -> is_mutual t'
                | uu____2572 -> false
              
              and exists_mutual uu___80_2573 =
                match uu___80_2573 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____2590 =
                let uu____2591 = FStar_Syntax_Subst.compress dt1  in
                uu____2591.FStar_Syntax_Syntax.n  in
              match uu____2590 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2597) ->
                  let dbs1 =
                    let uu____2612 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    Prims.snd uu____2612  in
                  let dbs2 =
                    let uu____2634 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____2634 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____2646 =
                               let uu____2647 =
                                 let uu____2648 =
                                   FStar_Syntax_Syntax.as_arg
                                     (Prims.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____2648]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____2647
                                in
                             uu____2646 None FStar_Range.dummyRange  in
                           let haseq_sort1 =
                             let uu____2654 = is_mutual sort  in
                             if uu____2654
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
                           let uu____2661 =
                             let uu____2662 =
                               let uu____2663 =
                                 let uu____2664 =
                                   let uu____2665 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((Prims.fst b), None)] uu____2665 None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____2664  in
                               [uu____2663]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____2662
                              in
                           uu____2661 None FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____2682 -> acc
  
let unoptimized_haseq_ty all_datas_in_the_bundle mutuals usubst us acc ty =
  let uu____2725 =
    match ty with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2737,bs,t,uu____2740,d_lids,uu____2742,uu____2743) ->
        (lid, bs, t, d_lids)
    | uu____2751 -> failwith "Impossible!"  in
  match uu____2725 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
      let t1 =
        let uu____2767 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst  in
        FStar_Syntax_Subst.subst uu____2767 t  in
      let uu____2774 = FStar_Syntax_Subst.open_term bs1 t1  in
      (match uu____2774 with
       | (bs2,t2) ->
           let ibs =
             let uu____2785 =
               let uu____2786 = FStar_Syntax_Subst.compress t2  in
               uu____2786.FStar_Syntax_Syntax.n  in
             match uu____2785 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2793) -> ibs
             | uu____2804 -> []  in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
           let ind =
             let uu____2809 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____2810 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us  in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2809 uu____2810  in
           let ind1 =
             let uu____2815 =
               let uu____2816 =
                 FStar_List.map
                   (fun uu____2821  ->
                      match uu____2821 with
                      | (bv,aq) ->
                          let uu____2828 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2828, aq)) bs2
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2816  in
             uu____2815 None FStar_Range.dummyRange  in
           let ind2 =
             let uu____2836 =
               let uu____2837 =
                 FStar_List.map
                   (fun uu____2842  ->
                      match uu____2842 with
                      | (bv,aq) ->
                          let uu____2849 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2849, aq)) ibs1
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2837  in
             uu____2836 None FStar_Range.dummyRange  in
           let haseq_ind =
             let uu____2857 =
               let uu____2858 =
                 let uu____2859 = FStar_Syntax_Syntax.as_arg ind2  in
                 [uu____2859]  in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2858
                in
             uu____2857 None FStar_Range.dummyRange  in
           let t_datas =
             FStar_List.filter
               (fun s  ->
                  match s with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____2867,uu____2868,uu____2869,t_lid,uu____2871,uu____2872,uu____2873,uu____2874)
                      -> t_lid = lid
                  | uu____2879 -> failwith "Impossible")
               all_datas_in_the_bundle
              in
           let data_cond =
             FStar_List.fold_left
               (unoptimized_haseq_data usubst bs2 haseq_ind mutuals)
               FStar_Syntax_Util.t_true t_datas
              in
           let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind  in
           let fml1 =
             let uu___85_2885 = fml  in
             let uu____2886 =
               let uu____2887 =
                 let uu____2892 =
                   let uu____2893 =
                     let uu____2900 =
                       let uu____2902 = FStar_Syntax_Syntax.as_arg haseq_ind
                          in
                       [uu____2902]  in
                     [uu____2900]  in
                   FStar_Syntax_Syntax.Meta_pattern uu____2893  in
                 (fml, uu____2892)  in
               FStar_Syntax_Syntax.Tm_meta uu____2887  in
             {
               FStar_Syntax_Syntax.n = uu____2886;
               FStar_Syntax_Syntax.tk = (uu___85_2885.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___85_2885.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___85_2885.FStar_Syntax_Syntax.vars)
             }  in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2914 =
                      let uu____2915 =
                        let uu____2916 =
                          let uu____2917 =
                            let uu____2918 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2918 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2917  in
                        [uu____2916]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2915
                       in
                    uu____2914 None FStar_Range.dummyRange) ibs1 fml1
              in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2940 =
                      let uu____2941 =
                        let uu____2942 =
                          let uu____2943 =
                            let uu____2944 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2944 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2943  in
                        [uu____2942]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2941
                       in
                    uu____2940 None FStar_Range.dummyRange) bs2 fml2
              in
           FStar_Syntax_Util.mk_conj acc fml3)
  
let unoptimized_haseq_scheme :
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
                       (lid,uu____3013,uu____3014,uu____3015,uu____3016,uu____3017,uu____3018,uu____3019)
                       -> lid
                   | uu____3026 -> failwith "Impossible!") tcs
               in
            let uu____3027 =
              let ty = FStar_List.hd tcs  in
              match ty with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____3035,uu____3036,uu____3037,uu____3038,uu____3039,uu____3040)
                  -> (lid, us)
              | uu____3047 -> failwith "Impossible!"  in
            match uu____3027 with
            | (lid,us) ->
                let uu____3053 = FStar_Syntax_Subst.univ_var_opening us  in
                (match uu____3053 with
                 | (usubst,us1) ->
                     let fml =
                       FStar_List.fold_left
                         (unoptimized_haseq_ty datas mutuals usubst us1)
                         FStar_Syntax_Util.t_true tcs
                        in
                     let env =
                       FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
                     ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                        "haseq";
                      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                        env sig_bndle;
                      (let env1 =
                         FStar_TypeChecker_Env.push_univ_vars env us1  in
                       let se =
                         let uu____3071 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")])
                            in
                         tc_assume env1 uu____3071 fml []
                           FStar_Range.dummyRange
                          in
                       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                         "haseq";
                       [se])))
  
let check_inductive_well_typedness :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list
            * FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let uu____3101 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___81_3111  ->
                    match uu___81_3111 with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____3112 ->
                        true
                    | uu____3124 -> false))
             in
          match uu____3101 with
          | (tys,datas) ->
              ((let uu____3137 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___82_3139  ->
                          match uu___82_3139 with
                          | FStar_Syntax_Syntax.Sig_datacon uu____3140 ->
                              false
                          | uu____3151 -> true))
                   in
                if uu____3137
                then
                  let uu____3152 =
                    let uu____3153 =
                      let uu____3156 = FStar_TypeChecker_Env.get_range env
                         in
                      ("Mutually defined type contains a non-inductive element",
                        uu____3156)
                       in
                    FStar_Errors.Error uu____3153  in
                  Prims.raise uu____3152
                else ());
               (let env0 = env  in
                let uu____3159 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____3173  ->
                         match uu____3173 with
                         | (env1,all_tcs,g) ->
                             let uu____3195 = tc_tycon env1 tc  in
                             (match uu____3195 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u
                                     in
                                  ((let uu____3212 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low
                                       in
                                    if uu____3212
                                    then
                                      let uu____3213 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1
                                         in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____3213
                                    else ());
                                   (let uu____3215 =
                                      let uu____3216 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g'
                                         in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____3216
                                       in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____3215))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard)
                   in
                match uu____3159 with
                | (env1,tcs,g) ->
                    let uu____3241 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____3249  ->
                             match uu____3249 with
                             | (datas1,g1) ->
                                 let uu____3260 =
                                   let uu____3263 = tc_data env1 tcs  in
                                   uu____3263 se  in
                                 (match uu____3260 with
                                  | (data,g') ->
                                      let uu____3273 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g'
                                         in
                                      ((data :: datas1), uu____3273))) datas
                        ([], g)
                       in
                    (match uu____3241 with
                     | (datas1,g1) ->
                         let uu____3285 =
                           generalize_and_inst_within env0 g1 tcs datas1  in
                         (match uu____3285 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____3302 =
                                  let uu____3310 =
                                    FStar_TypeChecker_Env.get_range env0  in
                                  ((FStar_List.append tcs1 datas2), quals,
                                    lids, uu____3310)
                                   in
                                FStar_Syntax_Syntax.Sig_bundle uu____3302  in
                              (sig_bndle, tcs1, datas2)))))
  