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
                                     FStar_Syntax_Util.maybe_tot_arrow
                                       indices1 t1
                                      in
                                   let uu____100 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____100 with
                                    | (t_type,u) ->
                                        ((let uu____110 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type
                                             in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____110);
                                         (let t_tc =
                                            FStar_Syntax_Util.maybe_tot_arrow
                                              (FStar_List.append tps2
                                                 indices1) t1
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
                                          let uu____117 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc)
                                             in
                                          (uu____117,
                                            (FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc, [], tps3, k3, mutuals,
                                                 data, quals, r)), u, guard)))))))))
      | uu____123 -> failwith "impossible"
  
let tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun tcs  ->
      fun uu___77_148  ->
        match uu___77_148 with
        | FStar_Syntax_Syntax.Sig_datacon
            (c,_uvs,t,tc_lid,ntps,quals,_mutual_tcs,r) ->
            let uu____164 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____178  ->
                     match uu____178 with
                     | (se,u_tc) ->
                         let uu____187 =
                           let uu____188 =
                             let uu____189 =
                               FStar_Syntax_Util.lid_of_sigelt se  in
                             FStar_Util.must uu____189  in
                           FStar_Ident.lid_equals tc_lid uu____188  in
                         if uu____187
                         then
                           (match se with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____199,uu____200,tps,uu____202,uu____203,uu____204,uu____205,uu____206)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____227  ->
                                          match uu____227 with
                                          | (x,uu____234) ->
                                              (x,
                                                (Some
                                                   FStar_Syntax_Syntax.imp_tag))))
                                   in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1  in
                                let uu____237 =
                                  let uu____241 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2
                                     in
                                  (uu____241, tps2, u_tc)  in
                                Some uu____237
                            | uu____245 -> failwith "Impossible")
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
            (match uu____164 with
             | (env1,tps,u_tc) ->
                 let uu____284 =
                   let uu____287 =
                     let uu____288 = FStar_Syntax_Subst.compress t  in
                     uu____288.FStar_Syntax_Syntax.n  in
                   match uu____287 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____305 = FStar_Util.first_N ntps bs  in
                       (match uu____305 with
                        | (uu____318,bs') ->
                            let t1 =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_arrow (bs', res)))
                                None t.FStar_Syntax_Syntax.pos
                               in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____354  ->
                                        match uu____354 with
                                        | (x,uu____358) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x)))
                               in
                            let uu____359 =
                              FStar_Syntax_Subst.subst subst1 t1  in
                            FStar_TypeChecker_Util.arrow_formals env1
                              uu____359)
                   | uu____360 -> ([], t)  in
                 (match uu____284 with
                  | (arguments,result) ->
                      ((let uu____371 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low
                           in
                        if uu____371
                        then
                          let uu____372 = FStar_Syntax_Print.lid_to_string c
                             in
                          let uu____373 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments
                             in
                          let uu____374 =
                            FStar_Syntax_Print.term_to_string result  in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____372
                            uu____373 uu____374
                        else ());
                       (let uu____376 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments
                           in
                        match uu____376 with
                        | (arguments1,env',us) ->
                            let uu____385 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result
                               in
                            (match uu____385 with
                             | (result1,res_lcomp) ->
                                 ((let uu____393 =
                                     let uu____394 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.lcomp_res_typ
                                        in
                                     uu____394.FStar_Syntax_Syntax.n  in
                                   match uu____393 with
                                   | FStar_Syntax_Syntax.Tm_type uu____397 ->
                                       ()
                                   | ty ->
                                       let uu____399 =
                                         let uu____400 =
                                           let uu____403 =
                                             let uu____404 =
                                               FStar_Syntax_Print.term_to_string
                                                 result1
                                                in
                                             let uu____405 =
                                               FStar_Syntax_Print.term_to_string
                                                 res_lcomp.FStar_Syntax_Syntax.lcomp_res_typ
                                                in
                                             FStar_Util.format2
                                               "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                               uu____404 uu____405
                                              in
                                           (uu____403, r)  in
                                         FStar_Errors.Error uu____400  in
                                       Prims.raise uu____399);
                                  (let uu____406 =
                                     FStar_Syntax_Util.head_and_args result1
                                      in
                                   match uu____406 with
                                   | (head1,uu____419) ->
                                       ((let uu____435 =
                                           let uu____436 =
                                             FStar_Syntax_Subst.compress
                                               head1
                                              in
                                           uu____436.FStar_Syntax_Syntax.n
                                            in
                                         match uu____435 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____440 ->
                                             let uu____441 =
                                               let uu____442 =
                                                 let uu____445 =
                                                   let uu____446 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       tc_lid
                                                      in
                                                   let uu____447 =
                                                     FStar_Syntax_Print.term_to_string
                                                       head1
                                                      in
                                                   FStar_Util.format2
                                                     "Expected a constructor of type %s; got %s"
                                                     uu____446 uu____447
                                                    in
                                                 (uu____445, r)  in
                                               FStar_Errors.Error uu____442
                                                in
                                             Prims.raise uu____441);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____452  ->
                                                  fun u_x  ->
                                                    match uu____452 with
                                                    | (x,uu____457) ->
                                                        let uu____458 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc
                                                           in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____458)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us
                                            in
                                         let t1 =
                                           let uu____460 =
                                             let uu____461 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____475  ->
                                                       match uu____475 with
                                                       | (x,uu____482) ->
                                                           (x,
                                                             (Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true)))))
                                                in
                                             FStar_List.append uu____461
                                               arguments1
                                              in
                                           FStar_Syntax_Util.maybe_tot_arrow
                                             uu____460 result1
                                            in
                                         ((FStar_Syntax_Syntax.Sig_datacon
                                             (c, [], t1, tc_lid, ntps, quals,
                                               [], r)), g))))))))))
        | uu____490 -> failwith "impossible"
  
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
            let uu___83_526 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___83_526.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___83_526.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (Prims.snd g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___83_526.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____532 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____532
           then
             let uu____533 = FStar_TypeChecker_Rel.guard_to_string env g1  in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____533
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____544  ->
                     match uu____544 with
                     | (se,uu____548) ->
                         (match se with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____549,uu____550,tps,k,uu____553,uu____554,uu____555,uu____556)
                              ->
                              let uu____563 =
                                FStar_Syntax_Util.maybe_tot_arrow tps k  in
                              FStar_Syntax_Syntax.null_binder uu____563
                          | uu____564 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun uu___78_569  ->
                     match uu___78_569 with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____570,uu____571,t,uu____573,uu____574,uu____575,uu____576,uu____577)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____582 -> failwith "Impossible"))
              in
           let t =
             FStar_Syntax_Util.maybe_tot_arrow
               (FStar_List.append binders binders')
               FStar_TypeChecker_Common.t_unit
              in
           (let uu____585 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____585
            then
              let uu____586 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____586
            else ());
           (let uu____588 = FStar_TypeChecker_Util.generalize_universes env t
               in
            match uu____588 with
            | (uvs,t1) ->
                ((let uu____598 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____598
                  then
                    let uu____599 =
                      let uu____600 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____600
                        (FStar_String.concat ", ")
                       in
                    let uu____606 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____599 uu____606
                  else ());
                 (let uu____608 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____608 with
                  | (uvs1,t2) ->
                      let uu____617 =
                        FStar_TypeChecker_Util.arrow_formals env t2  in
                      (match uu____617 with
                       | (args,uu____625) ->
                           let uu____626 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____626 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____663  ->
                                       fun uu____664  ->
                                         match (uu____663, uu____664) with
                                         | ((x,uu____674),(se,uu____676)) ->
                                             (match se with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____682,tps,uu____684,mutuals,datas1,quals,r)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____696 =
                                                    let uu____702 =
                                                      let uu____703 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____703.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____702 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____723 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____723 with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_TypeChecker_Env.result_typ
                                                                    env c
                                                               | uu____760 ->
                                                                   let uu____764
                                                                    =
                                                                    FStar_ST.read
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk
                                                                     in
                                                                   (FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c)))
                                                                    uu____764
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____785 -> ([], ty)
                                                     in
                                                  (match uu____696 with
                                                   | (tps1,t3) ->
                                                       FStar_Syntax_Syntax.Sig_inductive_typ
                                                         (tc, uvs1, tps1, t3,
                                                           mutuals, datas1,
                                                           quals, r))
                                              | uu____805 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____809 ->
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
                                             (fun uu___79_826  ->
                                                match uu___79_826 with
                                                | FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc,uu____831,uu____832,uu____833,uu____834,uu____835,uu____836,uu____837)
                                                    -> (tc, uvs_universes)
                                                | uu____845 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____851  ->
                                           fun d  ->
                                             match uu____851 with
                                             | (t3,uu____856) ->
                                                 (match d with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____858,uu____859,tc,ntps,quals,mutuals,r)
                                                      ->
                                                      let ty =
                                                        let uu____870 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____870
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      FStar_Syntax_Syntax.Sig_datacon
                                                        (l, uvs1, ty, tc,
                                                          ntps, quals,
                                                          mutuals, r)
                                                  | uu____873 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____882 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____882
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____890 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____890
  
let try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes)
  =
  fun t  ->
    let uu____899 =
      let uu____900 = FStar_Syntax_Subst.compress t  in
      uu____900.FStar_Syntax_Syntax.n  in
    match uu____899 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____916 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____919 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____938 = FStar_ST.read unfolded  in
          FStar_List.existsML
            (fun uu____950  ->
               match uu____950 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____970 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        Prims.fst uu____970  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (Prims.fst a) (Prims.fst a'))) true args
                        l)) uu____938
  
let rec ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1065 =
             let uu____1066 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____1066
              in
           debug_log env uu____1065);
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
           (let uu____1069 =
              let uu____1070 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1070
               in
            debug_log env uu____1069);
           (let uu____1071 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____1071) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1073 =
                  let uu____1074 = FStar_Syntax_Subst.compress btype1  in
                  uu____1074.FStar_Syntax_Syntax.n  in
                match uu____1073 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1093 = try_get_fv t  in
                    (match uu____1093 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1105  ->
                                 match uu____1105 with
                                 | (t1,uu____1109) ->
                                     let uu____1110 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____1110) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____1130 =
                        let uu____1131 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        Prims.op_Negation uu____1131  in
                      if uu____1130
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking strict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____1137  ->
                               match uu____1137 with
                               | (b,uu____1141) ->
                                   let uu____1142 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____1142) sbs)
                           &&
                           ((let uu____1143 =
                               let uu____1146 =
                                 FStar_TypeChecker_Env.result_typ env c  in
                               FStar_Syntax_Subst.open_term sbs uu____1146
                                in
                             match uu____1143 with
                             | (uu____1147,return_type) ->
                                 let uu____1149 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____1149)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____1150 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____1152 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____1155) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____1162) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____1168,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____1203  ->
                          match uu____1203 with
                          | (p,uu____1211,t) ->
                              let bs =
                                let uu____1221 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____1221
                                 in
                              let uu____1223 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____1223 with
                               | (bs1,t1) ->
                                   let uu____1228 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____1228)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1230,uu____1231)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____1251 ->
                    ((let uu____1253 =
                        let uu____1254 =
                          let uu____1255 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____1256 =
                            let uu____1257 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____1257  in
                          Prims.strcat uu____1255 uu____1256  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____1254
                         in
                      debug_log env uu____1253);
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
              (let uu____1265 =
                 let uu____1266 =
                   let uu____1267 =
                     let uu____1268 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____1268  in
                   Prims.strcat ilid.FStar_Ident.str uu____1267  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____1266
                  in
               debug_log env uu____1265);
              (let uu____1269 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____1269 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____1279 =
                        already_unfolded ilid args unfolded env  in
                      if uu____1279
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid
                            in
                         (let uu____1284 =
                            let uu____1285 =
                              let uu____1286 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____1286
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____1285
                             in
                          debug_log env uu____1284);
                         (let uu____1288 =
                            let uu____1289 = FStar_ST.read unfolded  in
                            let uu____1293 =
                              let uu____1297 =
                                let uu____1305 =
                                  let uu____1311 =
                                    FStar_List.splitAt num_ibs args  in
                                  Prims.fst uu____1311  in
                                (ilid, uu____1305)  in
                              [uu____1297]  in
                            FStar_List.append uu____1289 uu____1293  in
                          FStar_ST.write unfolded uu____1288);
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
                  (let uu____1369 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____1369 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Unionfind.change u'' (Some u)
                               | uu____1381 ->
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
                         (let uu____1384 =
                            let uu____1385 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____1385
                             in
                          debug_log env uu____1384);
                         (let uu____1386 =
                            let uu____1387 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____1387.FStar_Syntax_Syntax.n  in
                          match uu____1386 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____1403 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____1403 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____1430 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____1430 dbs1
                                       in
                                    let c1 =
                                      let uu____1433 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____1433 c
                                       in
                                    let uu____1435 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____1435 with
                                     | (args1,uu____1453) ->
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
                                           let uu____1499 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____1499 c1
                                            in
                                         ((let uu____1507 =
                                             let uu____1508 =
                                               let uu____1509 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____1510 =
                                                 let uu____1511 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____1511
                                                  in
                                               Prims.strcat uu____1509
                                                 uu____1510
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____1508
                                              in
                                           debug_log env uu____1507);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____1512 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____1514 =
                                  let uu____1515 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____1515.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____1514
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
                   (let uu____1541 = try_get_fv t1  in
                    match uu____1541 with
                    | (fv,uu____1545) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____1564 =
                      let uu____1565 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____1565
                       in
                    debug_log env uu____1564);
                   (let uu____1566 =
                      FStar_List.fold_left
                        (fun uu____1573  ->
                           fun b  ->
                             match uu____1573 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____1586 =
                                      ty_strictly_positive_in_type ty_lid
                                        (Prims.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____1587 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____1586, uu____1587))) (true, env)
                        sbs
                       in
                    match uu____1566 with | (b,uu____1593) -> b))
              | uu____1594 ->
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
              let uu____1613 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____1613 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Unionfind.change u'' (Some u)
                          | uu____1625 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____1627 =
                      let uu____1628 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____1628
                       in
                    debug_log env uu____1627);
                   (let uu____1629 =
                      let uu____1630 = FStar_Syntax_Subst.compress dt  in
                      uu____1630.FStar_Syntax_Syntax.n  in
                    match uu____1629 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____1633 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1636) ->
                        let dbs1 =
                          let uu____1651 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          Prims.snd uu____1651  in
                        let dbs2 =
                          let uu____1673 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____1673 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____1677 =
                            let uu____1678 =
                              let uu____1679 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____1679 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____1678
                             in
                          debug_log env uu____1677);
                         (let uu____1685 =
                            FStar_List.fold_left
                              (fun uu____1692  ->
                                 fun b  ->
                                   match uu____1692 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____1705 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (Prims.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____1706 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____1705, uu____1706)))
                              (true, env) dbs3
                             in
                          match uu____1685 with | (b,uu____1712) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____1713,uu____1714) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | uu____1730 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env_t -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____1748 =
        match ty with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____1758,uu____1759,uu____1760,uu____1761,uu____1762)
            -> (lid, us, bs)
        | uu____1769 -> failwith "Impossible!"  in
      match uu____1748 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____1776 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____1776 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____1791 =
                 let uu____1793 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 Prims.snd uu____1793  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____1799 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____1799
                      unfolded_inductives env2) uu____1791)
  
let datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1806,uu____1807,t,uu____1809,uu____1810,uu____1811,uu____1812,uu____1813)
        -> t
    | uu____1818 -> failwith "Impossible!"
  
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
          let uu____1835 =
            let uu____1836 = FStar_Syntax_Subst.compress dt1  in
            uu____1836.FStar_Syntax_Syntax.n  in
          match uu____1835 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1840) ->
              let dbs1 =
                let uu____1855 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                Prims.snd uu____1855  in
              let dbs2 =
                let uu____1877 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____1877 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____1886 =
                           let uu____1887 =
                             let uu____1888 =
                               FStar_Syntax_Syntax.as_arg
                                 (Prims.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____1888]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____1887
                            in
                         uu____1886 None FStar_Range.dummyRange  in
                       let sort_range =
                         ((Prims.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____1895 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add the 'noeq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____1895 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____1900 =
                       let uu____1901 =
                         let uu____1902 =
                           let uu____1903 =
                             let uu____1904 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs [((Prims.fst b), None)]
                               uu____1904 None
                              in
                           FStar_Syntax_Syntax.as_arg uu____1903  in
                         [uu____1902]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____1901
                        in
                     uu____1900 None FStar_Range.dummyRange) dbs3 cond
          | uu____1921 -> FStar_Syntax_Util.t_true
  
let optimized_haseq_ty all_datas_in_the_bundle usubst us acc ty =
  let uu____1980 =
    match ty with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____1992,bs,t,uu____1995,d_lids,uu____1997,uu____1998) ->
        (lid, bs, t, d_lids)
    | uu____2006 -> failwith "Impossible!"  in
  match uu____1980 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
      let t1 =
        let uu____2031 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst  in
        FStar_Syntax_Subst.subst uu____2031 t  in
      let uu____2038 = FStar_Syntax_Subst.open_term bs1 t1  in
      (match uu____2038 with
       | (bs2,t2) ->
           let ibs =
             let uu____2058 =
               let uu____2059 = FStar_Syntax_Subst.compress t2  in
               uu____2059.FStar_Syntax_Syntax.n  in
             match uu____2058 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2066) -> ibs
             | uu____2077 -> []  in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
           let ind =
             let uu____2082 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____2083 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us  in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2082 uu____2083  in
           let ind1 =
             let uu____2088 =
               let uu____2089 =
                 FStar_List.map
                   (fun uu____2094  ->
                      match uu____2094 with
                      | (bv,aq) ->
                          let uu____2101 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2101, aq)) bs2
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2089  in
             uu____2088 None FStar_Range.dummyRange  in
           let ind2 =
             let uu____2109 =
               let uu____2110 =
                 FStar_List.map
                   (fun uu____2115  ->
                      match uu____2115 with
                      | (bv,aq) ->
                          let uu____2122 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2122, aq)) ibs1
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2110  in
             uu____2109 None FStar_Range.dummyRange  in
           let haseq_ind =
             let uu____2130 =
               let uu____2131 =
                 let uu____2132 = FStar_Syntax_Syntax.as_arg ind2  in
                 [uu____2132]  in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2131
                in
             uu____2130 None FStar_Range.dummyRange  in
           let bs' =
             FStar_List.filter
               (fun b  ->
                  let uu____2146 = acc  in
                  match uu____2146 with
                  | (uu____2154,en,uu____2156,uu____2157) ->
                      let opt =
                        let uu____2166 =
                          let uu____2167 = FStar_Syntax_Util.type_u ()  in
                          Prims.fst uu____2167  in
                        FStar_TypeChecker_Rel.try_subtype' en
                          (Prims.fst b).FStar_Syntax_Syntax.sort uu____2166
                          false
                         in
                      (match opt with
                       | None  -> false
                       | Some uu____2170 -> true)) bs2
              in
           let haseq_bs =
             FStar_List.fold_left
               (fun t3  ->
                  fun b  ->
                    let uu____2174 =
                      let uu____2175 =
                        let uu____2176 =
                          let uu____2177 =
                            let uu____2178 =
                              FStar_Syntax_Syntax.bv_to_name (Prims.fst b)
                               in
                            FStar_Syntax_Syntax.as_arg uu____2178  in
                          [uu____2177]  in
                        FStar_Syntax_Syntax.mk_Tm_app
                          FStar_Syntax_Util.t_haseq uu____2176
                         in
                      uu____2175 None FStar_Range.dummyRange  in
                    FStar_Syntax_Util.mk_conj t3 uu____2174)
               FStar_Syntax_Util.t_true bs'
              in
           let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
           let fml1 =
             let uu___84_2187 = fml  in
             let uu____2188 =
               let uu____2189 =
                 let uu____2194 =
                   let uu____2195 =
                     let uu____2202 =
                       let uu____2204 = FStar_Syntax_Syntax.as_arg haseq_ind
                          in
                       [uu____2204]  in
                     [uu____2202]  in
                   FStar_Syntax_Syntax.Meta_pattern uu____2195  in
                 (fml, uu____2194)  in
               FStar_Syntax_Syntax.Tm_meta uu____2189  in
             {
               FStar_Syntax_Syntax.n = uu____2188;
               FStar_Syntax_Syntax.tk = (uu___84_2187.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___84_2187.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___84_2187.FStar_Syntax_Syntax.vars)
             }  in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2216 =
                      let uu____2217 =
                        let uu____2218 =
                          let uu____2219 =
                            let uu____2220 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2220 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2219  in
                        [uu____2218]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2217
                       in
                    uu____2216 None FStar_Range.dummyRange) ibs1 fml1
              in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2242 =
                      let uu____2243 =
                        let uu____2244 =
                          let uu____2245 =
                            let uu____2246 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2246 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2245  in
                        [uu____2244]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2243
                       in
                    uu____2242 None FStar_Range.dummyRange) bs2 fml2
              in
           let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3  in
           let uu____2266 = acc  in
           (match uu____2266 with
            | (l_axioms,env,guard',cond') ->
                let env1 = FStar_TypeChecker_Env.push_binders env bs2  in
                let env2 = FStar_TypeChecker_Env.push_binders env1 ibs1  in
                let t_datas =
                  FStar_List.filter
                    (fun s  ->
                       match s with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____2300,uu____2301,uu____2302,t_lid,uu____2304,uu____2305,uu____2306,uu____2307)
                           -> t_lid = lid
                       | uu____2312 -> failwith "Impossible")
                    all_datas_in_the_bundle
                   in
                let cond =
                  FStar_List.fold_left
                    (fun acc1  ->
                       fun d  ->
                         let uu____2316 =
                           optimized_haseq_soundness_for_data lid d usubst
                             bs2
                            in
                         FStar_Syntax_Util.mk_conj acc1 uu____2316)
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
                let uu____2318 = FStar_Syntax_Util.mk_conj guard' guard  in
                let uu____2321 = FStar_Syntax_Util.mk_conj cond' cond  in
                ((FStar_List.append l_axioms [(axiom_lid, fml3)]), env2,
                  uu____2318, uu____2321)))
  
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
                  (uu____2387,us,uu____2389,uu____2390,uu____2391,uu____2392,uu____2393,uu____2394)
                  -> us
              | uu____2401 -> failwith "Impossible!"  in
            let uu____2402 = FStar_Syntax_Subst.univ_var_opening us  in
            match uu____2402 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                   in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                  let uu____2418 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs
                     in
                  match uu____2418 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond  in
                      let uu____2450 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                         in
                      (match uu____2450 with
                       | (phi1,uu____2455) ->
                           ((let uu____2457 =
                               FStar_TypeChecker_Env.should_verify env2  in
                             if uu____2457
                             then
                               let uu____2458 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1)
                                  in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____2458
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____2466  ->
                                      match uu____2466 with
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
                let uu____2509 =
                  let uu____2510 = FStar_Syntax_Subst.compress t  in
                  uu____2510.FStar_Syntax_Syntax.n  in
                match uu____2509 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____2520) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____2547 = is_mutual t'  in
                    if uu____2547
                    then true
                    else
                      (let uu____2549 = FStar_List.map Prims.fst args  in
                       exists_mutual uu____2549)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____2562) -> is_mutual t'
                | uu____2567 -> false
              
              and exists_mutual uu___80_2568 =
                match uu___80_2568 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____2585 =
                let uu____2586 = FStar_Syntax_Subst.compress dt1  in
                uu____2586.FStar_Syntax_Syntax.n  in
              match uu____2585 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2592) ->
                  let dbs1 =
                    let uu____2607 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    Prims.snd uu____2607  in
                  let dbs2 =
                    let uu____2629 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____2629 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____2641 =
                               let uu____2642 =
                                 let uu____2643 =
                                   FStar_Syntax_Syntax.as_arg
                                     (Prims.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____2643]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____2642
                                in
                             uu____2641 None FStar_Range.dummyRange  in
                           let haseq_sort1 =
                             let uu____2649 = is_mutual sort  in
                             if uu____2649
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
                           let uu____2656 =
                             let uu____2657 =
                               let uu____2658 =
                                 let uu____2659 =
                                   let uu____2660 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((Prims.fst b), None)] uu____2660 None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____2659  in
                               [uu____2658]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____2657
                              in
                           uu____2656 None FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____2677 -> acc
  
let unoptimized_haseq_ty all_datas_in_the_bundle mutuals usubst us acc ty =
  let uu____2720 =
    match ty with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2732,bs,t,uu____2735,d_lids,uu____2737,uu____2738) ->
        (lid, bs, t, d_lids)
    | uu____2746 -> failwith "Impossible!"  in
  match uu____2720 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
      let t1 =
        let uu____2762 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst  in
        FStar_Syntax_Subst.subst uu____2762 t  in
      let uu____2769 = FStar_Syntax_Subst.open_term bs1 t1  in
      (match uu____2769 with
       | (bs2,t2) ->
           let ibs =
             let uu____2780 =
               let uu____2781 = FStar_Syntax_Subst.compress t2  in
               uu____2781.FStar_Syntax_Syntax.n  in
             match uu____2780 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2788) -> ibs
             | uu____2799 -> []  in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
           let ind =
             let uu____2804 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____2805 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us  in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2804 uu____2805  in
           let ind1 =
             let uu____2810 =
               let uu____2811 =
                 FStar_List.map
                   (fun uu____2816  ->
                      match uu____2816 with
                      | (bv,aq) ->
                          let uu____2823 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2823, aq)) bs2
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2811  in
             uu____2810 None FStar_Range.dummyRange  in
           let ind2 =
             let uu____2831 =
               let uu____2832 =
                 FStar_List.map
                   (fun uu____2837  ->
                      match uu____2837 with
                      | (bv,aq) ->
                          let uu____2844 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2844, aq)) ibs1
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2832  in
             uu____2831 None FStar_Range.dummyRange  in
           let haseq_ind =
             let uu____2852 =
               let uu____2853 =
                 let uu____2854 = FStar_Syntax_Syntax.as_arg ind2  in
                 [uu____2854]  in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2853
                in
             uu____2852 None FStar_Range.dummyRange  in
           let t_datas =
             FStar_List.filter
               (fun s  ->
                  match s with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____2862,uu____2863,uu____2864,t_lid,uu____2866,uu____2867,uu____2868,uu____2869)
                      -> t_lid = lid
                  | uu____2874 -> failwith "Impossible")
               all_datas_in_the_bundle
              in
           let data_cond =
             FStar_List.fold_left
               (unoptimized_haseq_data usubst bs2 haseq_ind mutuals)
               FStar_Syntax_Util.t_true t_datas
              in
           let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind  in
           let fml1 =
             let uu___85_2880 = fml  in
             let uu____2881 =
               let uu____2882 =
                 let uu____2887 =
                   let uu____2888 =
                     let uu____2895 =
                       let uu____2897 = FStar_Syntax_Syntax.as_arg haseq_ind
                          in
                       [uu____2897]  in
                     [uu____2895]  in
                   FStar_Syntax_Syntax.Meta_pattern uu____2888  in
                 (fml, uu____2887)  in
               FStar_Syntax_Syntax.Tm_meta uu____2882  in
             {
               FStar_Syntax_Syntax.n = uu____2881;
               FStar_Syntax_Syntax.tk = (uu___85_2880.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___85_2880.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___85_2880.FStar_Syntax_Syntax.vars)
             }  in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2909 =
                      let uu____2910 =
                        let uu____2911 =
                          let uu____2912 =
                            let uu____2913 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2913 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2912  in
                        [uu____2911]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2910
                       in
                    uu____2909 None FStar_Range.dummyRange) ibs1 fml1
              in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2935 =
                      let uu____2936 =
                        let uu____2937 =
                          let uu____2938 =
                            let uu____2939 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2939 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2938  in
                        [uu____2937]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2936
                       in
                    uu____2935 None FStar_Range.dummyRange) bs2 fml2
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
                       (lid,uu____3008,uu____3009,uu____3010,uu____3011,uu____3012,uu____3013,uu____3014)
                       -> lid
                   | uu____3021 -> failwith "Impossible!") tcs
               in
            let uu____3022 =
              let ty = FStar_List.hd tcs  in
              match ty with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____3030,uu____3031,uu____3032,uu____3033,uu____3034,uu____3035)
                  -> (lid, us)
              | uu____3042 -> failwith "Impossible!"  in
            match uu____3022 with
            | (lid,us) ->
                let uu____3048 = FStar_Syntax_Subst.univ_var_opening us  in
                (match uu____3048 with
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
                         let uu____3066 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")])
                            in
                         tc_assume env1 uu____3066 fml []
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
          let uu____3096 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___81_3106  ->
                    match uu___81_3106 with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____3107 ->
                        true
                    | uu____3119 -> false))
             in
          match uu____3096 with
          | (tys,datas) ->
              ((let uu____3132 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___82_3134  ->
                          match uu___82_3134 with
                          | FStar_Syntax_Syntax.Sig_datacon uu____3135 ->
                              false
                          | uu____3146 -> true))
                   in
                if uu____3132
                then
                  let uu____3147 =
                    let uu____3148 =
                      let uu____3151 = FStar_TypeChecker_Env.get_range env
                         in
                      ("Mutually defined type contains a non-inductive element",
                        uu____3151)
                       in
                    FStar_Errors.Error uu____3148  in
                  Prims.raise uu____3147
                else ());
               (let env0 = env  in
                let uu____3154 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____3168  ->
                         match uu____3168 with
                         | (env1,all_tcs,g) ->
                             let uu____3190 = tc_tycon env1 tc  in
                             (match uu____3190 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u
                                     in
                                  ((let uu____3207 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low
                                       in
                                    if uu____3207
                                    then
                                      let uu____3208 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1
                                         in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____3208
                                    else ());
                                   (let uu____3210 =
                                      let uu____3211 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g'
                                         in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____3211
                                       in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____3210))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard)
                   in
                match uu____3154 with
                | (env1,tcs,g) ->
                    let uu____3236 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____3244  ->
                             match uu____3244 with
                             | (datas1,g1) ->
                                 let uu____3255 =
                                   let uu____3258 = tc_data env1 tcs  in
                                   uu____3258 se  in
                                 (match uu____3255 with
                                  | (data,g') ->
                                      let uu____3268 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g'
                                         in
                                      ((data :: datas1), uu____3268))) datas
                        ([], g)
                       in
                    (match uu____3236 with
                     | (datas1,g1) ->
                         let uu____3280 =
                           generalize_and_inst_within env0 g1 tcs datas1  in
                         (match uu____3280 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____3297 =
                                  let uu____3305 =
                                    FStar_TypeChecker_Env.get_range env0  in
                                  ((FStar_List.append tcs1 datas2), quals,
                                    lids, uu____3305)
                                   in
                                FStar_Syntax_Syntax.Sig_bundle uu____3297  in
                              (sig_bndle, tcs1, datas2)))))
  