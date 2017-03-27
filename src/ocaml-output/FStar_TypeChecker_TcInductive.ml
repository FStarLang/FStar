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
           | (tps,k) ->
               let uu____43 = FStar_TypeChecker_TcTerm.tc_binders env tps  in
               (match uu____43 with
                | (tps,env_tps,guard_params,us) ->
                    let uu____56 = FStar_TypeChecker_Util.arrow_formals env k
                       in
                    (match uu____56 with
                     | (indices,t) ->
                         let uu____65 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices
                            in
                         (match uu____65 with
                          | (indices,env',guard_indices,us') ->
                              let uu____78 =
                                let uu____81 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t
                                   in
                                match uu____81 with
                                | (t,uu____88,g) ->
                                    let _0_203 =
                                      let _0_202 =
                                        let _0_201 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g
                                           in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params _0_201
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' _0_202
                                       in
                                    (t, _0_203)
                                 in
                              (match uu____78 with
                               | (t,guard) ->
                                   let k =
                                     FStar_Syntax_Util.maybe_tot_arrow
                                       indices t
                                      in
                                   let uu____97 = FStar_Syntax_Util.type_u ()
                                      in
                                   (match uu____97 with
                                    | (t_type,u) ->
                                        ((let _0_204 =
                                            FStar_TypeChecker_Rel.teq env' t
                                              t_type
                                             in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' _0_204);
                                         (let t_tc =
                                            FStar_Syntax_Util.maybe_tot_arrow
                                              (FStar_List.append tps indices)
                                              t
                                             in
                                          let tps =
                                            FStar_Syntax_Subst.close_binders
                                              tps
                                             in
                                          let k =
                                            FStar_Syntax_Subst.close tps k
                                             in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              None
                                             in
                                          let _0_205 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc)
                                             in
                                          (_0_205,
                                            (FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc, [], tps, k, mutuals,
                                                 data, quals, r)), u, guard)))))))))
      | uu____118 -> failwith "impossible"
  
let tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun tcs  ->
      fun uu___77_143  ->
        match uu___77_143 with
        | FStar_Syntax_Syntax.Sig_datacon
            (c,_uvs,t,tc_lid,ntps,quals,_mutual_tcs,r) ->
            let uu____159 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____173  ->
                     match uu____173 with
                     | (se,u_tc) ->
                         let uu____182 =
                           let _0_206 =
                             FStar_Util.must
                               (FStar_Syntax_Util.lid_of_sigelt se)
                              in
                           FStar_Ident.lid_equals tc_lid _0_206  in
                         if uu____182
                         then
                           (match se with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____191,uu____192,tps,uu____194,uu____195,uu____196,uu____197,uu____198)
                                ->
                                let tps =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____219  ->
                                          match uu____219 with
                                          | (x,uu____226) ->
                                              (x,
                                                (Some
                                                   FStar_Syntax_Syntax.imp_tag))))
                                   in
                                let tps = FStar_Syntax_Subst.open_binders tps
                                   in
                                Some
                                  (let _0_207 =
                                     FStar_TypeChecker_Env.push_binders env
                                       tps
                                      in
                                   (_0_207, tps, u_tc))
                            | uu____232 -> failwith "Impossible")
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
            (match uu____159 with
             | (env,tps,u_tc) ->
                 let uu____271 =
                   let uu____274 =
                     (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                      in
                   match uu____274 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____289 = FStar_Util.first_N ntps bs  in
                       (match uu____289 with
                        | (uu____302,bs') ->
                            let t =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_arrow (bs', res)))
                                None t.FStar_Syntax_Syntax.pos
                               in
                            let subst =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____338  ->
                                        match uu____338 with
                                        | (x,uu____342) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x)))
                               in
                            let _0_208 = FStar_Syntax_Subst.subst subst t  in
                            FStar_TypeChecker_Util.arrow_formals env _0_208)
                   | uu____343 -> ([], t)  in
                 (match uu____271 with
                  | (arguments,result) ->
                      ((let uu____354 =
                          FStar_TypeChecker_Env.debug env FStar_Options.Low
                           in
                        if uu____354
                        then
                          let _0_211 = FStar_Syntax_Print.lid_to_string c  in
                          let _0_210 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments
                             in
                          let _0_209 =
                            FStar_Syntax_Print.term_to_string result  in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" _0_211
                            _0_210 _0_209
                        else ());
                       (let uu____356 =
                          FStar_TypeChecker_TcTerm.tc_tparams env arguments
                           in
                        match uu____356 with
                        | (arguments,env',us) ->
                            let uu____365 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result
                               in
                            (match uu____365 with
                             | (result,res_lcomp) ->
                                 ((let uu____373 =
                                     (FStar_Syntax_Subst.compress
                                        res_lcomp.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n
                                      in
                                   match uu____373 with
                                   | FStar_Syntax_Syntax.Tm_type uu____374 ->
                                       ()
                                   | ty ->
                                       Prims.raise
                                         (FStar_Errors.Error
                                            (let _0_214 =
                                               let _0_213 =
                                                 FStar_Syntax_Print.term_to_string
                                                   result
                                                  in
                                               let _0_212 =
                                                 FStar_Syntax_Print.term_to_string
                                                   res_lcomp.FStar_Syntax_Syntax.lcomp_res_typ
                                                  in
                                               FStar_Util.format2
                                                 "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                 _0_213 _0_212
                                                in
                                             (_0_214, r))));
                                  (let uu____376 =
                                     FStar_Syntax_Util.head_and_args result
                                      in
                                   match uu____376 with
                                   | (head,uu____389) ->
                                       ((let uu____405 =
                                           (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                                            in
                                         match uu____405 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____407 ->
                                             Prims.raise
                                               (FStar_Errors.Error
                                                  (let _0_217 =
                                                     let _0_216 =
                                                       FStar_Syntax_Print.lid_to_string
                                                         tc_lid
                                                        in
                                                     let _0_215 =
                                                       FStar_Syntax_Print.term_to_string
                                                         head
                                                        in
                                                     FStar_Util.format2
                                                       "Expected a constructor of type %s; got %s"
                                                       _0_216 _0_215
                                                      in
                                                   (_0_217, r))));
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____412  ->
                                                  fun u_x  ->
                                                    match uu____412 with
                                                    | (x,uu____417) ->
                                                        let _0_218 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc
                                                           in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g _0_218)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments us
                                            in
                                         let t =
                                           let _0_220 =
                                             let _0_219 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____431  ->
                                                       match uu____431 with
                                                       | (x,uu____438) ->
                                                           (x,
                                                             (Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true)))))
                                                in
                                             FStar_List.append _0_219
                                               arguments
                                              in
                                           FStar_Syntax_Util.maybe_tot_arrow
                                             _0_220 result
                                            in
                                         ((FStar_Syntax_Syntax.Sig_datacon
                                             (c, [], t, tc_lid, ntps, quals,
                                               [], r)), g))))))))))
        | uu____443 -> failwith "impossible"
  
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
          let g =
            let uu___83_479 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___83_479.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___83_479.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (Prims.snd g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___83_479.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____485 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____485
           then
             let _0_221 = FStar_TypeChecker_Rel.guard_to_string env g  in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               _0_221
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____496  ->
                     match uu____496 with
                     | (se,uu____500) ->
                         (match se with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____501,uu____502,tps,k,uu____505,uu____506,uu____507,uu____508)
                              ->
                              FStar_Syntax_Syntax.null_binder
                                (FStar_Syntax_Util.maybe_tot_arrow tps k)
                          | uu____515 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun uu___78_520  ->
                     match uu___78_520 with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____521,uu____522,t,uu____524,uu____525,uu____526,uu____527,uu____528)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____533 -> failwith "Impossible"))
              in
           let t =
             FStar_Syntax_Util.maybe_tot_arrow
               (FStar_List.append binders binders')
               FStar_TypeChecker_Common.t_unit
              in
           (let uu____536 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____536
            then
              let _0_222 = FStar_TypeChecker_Normalize.term_to_string env t
                 in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" _0_222
            else ());
           (let uu____538 = FStar_TypeChecker_Util.generalize_universes env t
               in
            match uu____538 with
            | (uvs,t) ->
                ((let uu____548 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____548
                  then
                    let _0_225 =
                      let _0_223 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right _0_223 (FStar_String.concat ", ")
                       in
                    let _0_224 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      _0_225 _0_224
                  else ());
                 (let uu____554 = FStar_Syntax_Subst.open_univ_vars uvs t  in
                  match uu____554 with
                  | (uvs,t) ->
                      let uu____563 =
                        FStar_TypeChecker_Util.arrow_formals env t  in
                      (match uu____563 with
                       | (args,uu____571) ->
                           let uu____572 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____572 with
                            | (tc_types,data_types) ->
                                let tcs =
                                  FStar_List.map2
                                    (fun uu____609  ->
                                       fun uu____610  ->
                                         match (uu____609, uu____610) with
                                         | ((x,uu____620),(se,uu____622)) ->
                                             (match se with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____628,tps,uu____630,mutuals,datas,quals,r)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____642 =
                                                    let uu____648 =
                                                      (FStar_Syntax_Subst.compress
                                                         ty).FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____648 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders,c) ->
                                                        let uu____666 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders
                                                           in
                                                        (match uu____666 with
                                                         | (tps,rest) ->
                                                             let t =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_TypeChecker_Env.result_typ
                                                                    env c
                                                               | uu____703 ->
                                                                   let _0_226
                                                                    =
                                                                    FStar_ST.read
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk
                                                                     in
                                                                   (FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c)))
                                                                    _0_226
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps, t))
                                                    | uu____726 -> ([], ty)
                                                     in
                                                  (match uu____642 with
                                                   | (tps,t) ->
                                                       FStar_Syntax_Syntax.Sig_inductive_typ
                                                         (tc, uvs, tps, t,
                                                           mutuals, datas,
                                                           quals, r))
                                              | uu____746 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas =
                                  match uvs with
                                  | [] -> datas
                                  | uu____750 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs
                                          (FStar_List.map
                                             (fun _0_227  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_227))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs
                                          (FStar_List.map
                                             (fun uu___79_767  ->
                                                match uu___79_767 with
                                                | FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc,uu____772,uu____773,uu____774,uu____775,uu____776,uu____777,uu____778)
                                                    -> (tc, uvs_universes)
                                                | uu____786 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____792  ->
                                           fun d  ->
                                             match uu____792 with
                                             | (t,uu____797) ->
                                                 (match d with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____799,uu____800,tc,ntps,quals,mutuals,r)
                                                      ->
                                                      let ty =
                                                        let _0_228 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          _0_228
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs)
                                                         in
                                                      FStar_Syntax_Syntax.Sig_datacon
                                                        (l, uvs, ty, tc,
                                                          ntps, quals,
                                                          mutuals, r)
                                                  | uu____813 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs, datas)))))))
  
let debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____822 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____822
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let _0_229 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid _0_229
  
let try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes)
  =
  fun t  ->
    let uu____837 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
    match uu____837 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
        (match t.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____851 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____854 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let _0_230 = FStar_ST.read unfolded  in
          FStar_List.existsML
            (fun uu____878  ->
               match uu____878 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        Prims.fst
                          (FStar_List.splitAt (FStar_List.length l) arrghs)
                         in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (Prims.fst a) (Prims.fst a'))) true args
                        l)) _0_230
  
let rec ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let _0_232 =
             let _0_231 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " _0_231  in
           debug_log env _0_232);
          (let btype =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype
              in
           (let _0_234 =
              let _0_233 = FStar_Syntax_Print.term_to_string btype  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                _0_233
               in
            debug_log env _0_234);
           (Prims.op_Negation (ty_occurs_in ty_lid btype)) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____983 =
                  (FStar_Syntax_Subst.compress btype).FStar_Syntax_Syntax.n
                   in
                match uu____983 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1000 = try_get_fv t  in
                    (match uu____1000 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1012  ->
                                 match uu____1012 with
                                 | (t,uu____1016) ->
                                     Prims.op_Negation
                                       (ty_occurs_in ty_lid t)) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____1036 =
                        Prims.op_Negation
                          (FStar_Syntax_Util.is_pure_or_ghost_comp c)
                         in
                      if uu____1036
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking strict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____1042  ->
                               match uu____1042 with
                               | (b,uu____1046) ->
                                   Prims.op_Negation
                                     (ty_occurs_in ty_lid
                                        b.FStar_Syntax_Syntax.sort)) sbs)
                           &&
                           ((let uu____1047 =
                               let _0_235 =
                                 FStar_TypeChecker_Env.result_typ env c  in
                               FStar_Syntax_Subst.open_term sbs _0_235  in
                             match uu____1047 with
                             | (uu____1050,return_type) ->
                                 let _0_236 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded _0_236)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____1052 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____1054 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____1057) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____1064) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____1070,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____1105  ->
                          match uu____1105 with
                          | (p,uu____1113,t) ->
                              let bs =
                                let _0_237 = FStar_Syntax_Syntax.pat_bvs p
                                   in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  _0_237
                                 in
                              let uu____1123 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____1123 with
                               | (bs,t) ->
                                   let _0_238 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   ty_strictly_positive_in_type ty_lid t
                                     unfolded _0_238)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1129,uu____1130)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____1150 ->
                    ((let _0_243 =
                        let _0_242 =
                          let _0_241 = FStar_Syntax_Print.tag_of_term btype
                             in
                          let _0_240 =
                            let _0_239 =
                              FStar_Syntax_Print.term_to_string btype  in
                            Prims.strcat " and term: " _0_239  in
                          Prims.strcat _0_241 _0_240  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          _0_242
                         in
                      debug_log env _0_243);
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
              (let _0_247 =
                 let _0_246 =
                   let _0_245 =
                     let _0_244 = FStar_Syntax_Print.args_to_string args  in
                     Prims.strcat " applied to arguments: " _0_244  in
                   Prims.strcat ilid.FStar_Ident.str _0_245  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   _0_246
                  in
               debug_log env _0_247);
              (let uu____1159 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____1159 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____1169 =
                        already_unfolded ilid args unfolded env  in
                      if uu____1169
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid
                            in
                         (let _0_250 =
                            let _0_249 =
                              let _0_248 = FStar_Util.string_of_int num_ibs
                                 in
                              Prims.strcat _0_248
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              _0_249
                             in
                          debug_log env _0_250);
                         (let _0_255 =
                            let _0_254 = FStar_ST.read unfolded  in
                            let _0_253 =
                              let _0_252 =
                                let _0_251 =
                                  Prims.fst (FStar_List.splitAt num_ibs args)
                                   in
                                (ilid, _0_251)  in
                              [_0_252]  in
                            FStar_List.append _0_254 _0_253  in
                          FStar_ST.write unfolded _0_255);
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
                  (let uu____1220 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____1220 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Unionfind.change u'' (Some u)
                               | uu____1232 ->
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
                             env dt
                            in
                         (let _0_257 =
                            let _0_256 = FStar_Syntax_Print.term_to_string dt
                               in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              _0_256
                             in
                          debug_log env _0_257);
                         (let uu____1235 =
                            (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
                             in
                          match uu____1235 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____1249 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____1249 with
                                | (ibs,dbs) ->
                                    let ibs =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs =
                                      let _0_258 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs
                                         in
                                      FStar_Syntax_Subst.subst_binders _0_258
                                        dbs
                                       in
                                    let c =
                                      let _0_259 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs
                                         in
                                      FStar_Syntax_Subst.subst_comp _0_259 c
                                       in
                                    let uu____1277 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____1277 with
                                     | (args,uu____1295) ->
                                         let subst =
                                           FStar_List.fold_left2
                                             (fun subst  ->
                                                fun ib  ->
                                                  fun arg  ->
                                                    FStar_List.append subst
                                                      [FStar_Syntax_Syntax.NT
                                                         ((Prims.fst ib),
                                                           (Prims.fst arg))])
                                             [] ibs args
                                            in
                                         let dbs =
                                           FStar_Syntax_Subst.subst_binders
                                             subst dbs
                                            in
                                         let c =
                                           let _0_260 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs) subst
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             _0_260 c
                                            in
                                         ((let _0_265 =
                                             let _0_264 =
                                               let _0_263 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs
                                                  in
                                               let _0_262 =
                                                 let _0_261 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c
                                                    in
                                                 Prims.strcat ", and c: "
                                                   _0_261
                                                  in
                                               Prims.strcat _0_263 _0_262  in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               _0_264
                                              in
                                           debug_log env _0_265);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs, c)) ilid num_ibs
                                            unfolded env))))
                          | uu____1347 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let _0_266 =
                                  (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
                                   in
                                ty_nested_positive_in_type ty_lid _0_266 ilid
                                  num_ibs unfolded env))))))

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
              | FStar_Syntax_Syntax.Tm_app (t,args) ->
                  (debug_log env
                     "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself";
                   (let uu____1372 = try_get_fv t  in
                    match uu____1372 with
                    | (fv,uu____1376) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let _0_268 =
                      let _0_267 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        _0_267
                       in
                    debug_log env _0_268);
                   (let uu____1395 =
                      FStar_List.fold_left
                        (fun uu____1402  ->
                           fun b  ->
                             match uu____1402 with
                             | (r,env) ->
                                 if Prims.op_Negation r
                                 then (r, env)
                                 else
                                   (let _0_270 =
                                      ty_strictly_positive_in_type ty_lid
                                        (Prims.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env
                                       in
                                    let _0_269 =
                                      FStar_TypeChecker_Env.push_binders env
                                        [b]
                                       in
                                    (_0_270, _0_269))) (true, env) sbs
                       in
                    match uu____1395 with | (b,uu____1420) -> b))
              | uu____1421 ->
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
              let uu____1440 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____1440 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Unionfind.change u'' (Some u)
                          | uu____1452 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let _0_272 =
                      let _0_271 = FStar_Syntax_Print.term_to_string dt  in
                      Prims.strcat "Checking data constructor type: " _0_271
                       in
                    debug_log env _0_272);
                   (let uu____1454 =
                      (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
                       in
                    match uu____1454 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____1455 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1458) ->
                        let dbs =
                          Prims.snd
                            (FStar_List.splitAt (FStar_List.length ty_bs) dbs)
                           in
                        let dbs =
                          let _0_273 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders _0_273 dbs  in
                        let dbs = FStar_Syntax_Subst.open_binders dbs  in
                        ((let _0_276 =
                            let _0_275 =
                              let _0_274 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs)
                                 in
                              Prims.strcat _0_274 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              _0_275
                             in
                          debug_log env _0_276);
                         (let uu____1493 =
                            FStar_List.fold_left
                              (fun uu____1500  ->
                                 fun b  ->
                                   match uu____1500 with
                                   | (r,env) ->
                                       if Prims.op_Negation r
                                       then (r, env)
                                       else
                                         (let _0_278 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (Prims.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env
                                             in
                                          let _0_277 =
                                            FStar_TypeChecker_Env.push_binders
                                              env [b]
                                             in
                                          (_0_278, _0_277))) (true, env) dbs
                             in
                          match uu____1493 with | (b,uu____1518) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____1519,uu____1520) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | uu____1536 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env_t -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____1554 =
        match ty with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____1564,uu____1565,uu____1566,uu____1567,uu____1568)
            -> (lid, us, bs)
        | uu____1575 -> failwith "Impossible!"  in
      match uu____1554 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____1582 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____1582 with
           | (ty_usubst,ty_us) ->
               let env = FStar_TypeChecker_Env.push_univ_vars env ty_us  in
               let env = FStar_TypeChecker_Env.push_binders env ty_bs  in
               let ty_bs = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs = FStar_Syntax_Subst.open_binders ty_bs  in
               let _0_280 =
                 Prims.snd (FStar_TypeChecker_Env.datacons_of_typ env ty_lid)
                  in
               FStar_List.for_all
                 (fun d  ->
                    let _0_279 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us
                       in
                    ty_positive_in_datacon ty_lid d ty_bs _0_279
                      unfolded_inductives env) _0_280)
  
let datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1605,uu____1606,t,uu____1608,uu____1609,uu____1610,uu____1611,uu____1612)
        -> t
    | uu____1617 -> failwith "Impossible!"
  
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
          let dt = FStar_Syntax_Subst.subst usubst dt  in
          let uu____1634 =
            (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n  in
          match uu____1634 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1636) ->
              let dbs =
                Prims.snd (FStar_List.splitAt (FStar_List.length bs) dbs)  in
              let dbs =
                let _0_281 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders _0_281 dbs  in
              let dbs = FStar_Syntax_Subst.open_binders dbs  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         (let _0_283 =
                            let _0_282 =
                              FStar_Syntax_Syntax.as_arg
                                (Prims.fst b).FStar_Syntax_Syntax.sort
                               in
                            [_0_282]  in
                          FStar_Syntax_Syntax.mk_Tm_app
                            FStar_Syntax_Util.t_haseq _0_283) None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((Prims.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b =
                         let _0_284 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add the 'noeq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label _0_284 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b)
                  FStar_Syntax_Util.t_true dbs
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     (let _0_287 =
                        let _0_286 =
                          FStar_Syntax_Syntax.as_arg
                            (let _0_285 = FStar_Syntax_Subst.close [b] t  in
                             FStar_Syntax_Util.abs [((Prims.fst b), None)]
                               _0_285 None)
                           in
                        [_0_286]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        _0_287) None FStar_Range.dummyRange) dbs cond
          | uu____1697 -> FStar_Syntax_Util.t_true
  
let optimized_haseq_ty all_datas_in_the_bundle usubst us acc ty =
  let uu____1756 =
    match ty with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____1768,bs,t,uu____1771,d_lids,uu____1773,uu____1774) ->
        (lid, bs, t, d_lids)
    | uu____1782 -> failwith "Impossible!"  in
  match uu____1756 with
  | (lid,bs,t,d_lids) ->
      let bs = FStar_Syntax_Subst.subst_binders usubst bs  in
      let t =
        let _0_288 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst  in
        FStar_Syntax_Subst.subst _0_288 t  in
      let uu____1812 = FStar_Syntax_Subst.open_term bs t  in
      (match uu____1812 with
       | (bs,t) ->
           let ibs =
             let uu____1832 =
               (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
             match uu____1832 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____1837) -> ibs
             | uu____1848 -> []  in
           let ibs = FStar_Syntax_Subst.open_binders ibs  in
           let ind =
             let _0_290 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let _0_289 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us  in
             FStar_Syntax_Syntax.mk_Tm_uinst _0_290 _0_289  in
           let ind =
             (let _0_292 =
                FStar_List.map
                  (fun uu____1865  ->
                     match uu____1865 with
                     | (bv,aq) ->
                         let _0_291 = FStar_Syntax_Syntax.bv_to_name bv  in
                         (_0_291, aq)) bs
                 in
              FStar_Syntax_Syntax.mk_Tm_app ind _0_292) None
               FStar_Range.dummyRange
              in
           let ind =
             (let _0_294 =
                FStar_List.map
                  (fun uu____1883  ->
                     match uu____1883 with
                     | (bv,aq) ->
                         let _0_293 = FStar_Syntax_Syntax.bv_to_name bv  in
                         (_0_293, aq)) ibs
                 in
              FStar_Syntax_Syntax.mk_Tm_app ind _0_294) None
               FStar_Range.dummyRange
              in
           let haseq_ind =
             (let _0_296 =
                let _0_295 = FStar_Syntax_Syntax.as_arg ind  in [_0_295]  in
              FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_296)
               None FStar_Range.dummyRange
              in
           let bs' =
             FStar_List.filter
               (fun b  ->
                  let uu____1906 = acc  in
                  match uu____1906 with
                  | (uu____1914,en,uu____1916,uu____1917) ->
                      let opt =
                        let _0_297 = Prims.fst (FStar_Syntax_Util.type_u ())
                           in
                        FStar_TypeChecker_Rel.try_subtype' en
                          (Prims.fst b).FStar_Syntax_Syntax.sort _0_297 false
                         in
                      (match opt with
                       | None  -> false
                       | Some uu____1926 -> true)) bs
              in
           let haseq_bs =
             FStar_List.fold_left
               (fun t  ->
                  fun b  ->
                    let _0_300 =
                      (let _0_299 =
                         let _0_298 =
                           FStar_Syntax_Syntax.as_arg
                             (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
                            in
                         [_0_298]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq _0_299) None
                        FStar_Range.dummyRange
                       in
                    FStar_Syntax_Util.mk_conj t _0_300)
               FStar_Syntax_Util.t_true bs'
              in
           let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
           let fml =
             let uu___84_1940 = fml  in
             let _0_304 =
               FStar_Syntax_Syntax.Tm_meta
                 (let _0_303 =
                    FStar_Syntax_Syntax.Meta_pattern
                      (let _0_302 =
                         let _0_301 = FStar_Syntax_Syntax.as_arg haseq_ind
                            in
                         [_0_301]  in
                       [_0_302])
                     in
                  (fml, _0_303))
                in
             {
               FStar_Syntax_Syntax.n = _0_304;
               FStar_Syntax_Syntax.tk = (uu___84_1940.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___84_1940.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___84_1940.FStar_Syntax_Syntax.vars)
             }  in
           let fml =
             FStar_List.fold_right
               (fun b  ->
                  fun t  ->
                    (let _0_307 =
                       let _0_306 =
                         FStar_Syntax_Syntax.as_arg
                           (let _0_305 = FStar_Syntax_Subst.close [b] t  in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              _0_305 None)
                          in
                       [_0_306]  in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                       _0_307) None FStar_Range.dummyRange) ibs fml
              in
           let fml =
             FStar_List.fold_right
               (fun b  ->
                  fun t  ->
                    (let _0_310 =
                       let _0_309 =
                         FStar_Syntax_Syntax.as_arg
                           (let _0_308 = FStar_Syntax_Subst.close [b] t  in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              _0_308 None)
                          in
                       [_0_309]  in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                       _0_310) None FStar_Range.dummyRange) bs fml
              in
           let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
           let uu____1992 = acc  in
           (match uu____1992 with
            | (l_axioms,env,guard',cond') ->
                let env = FStar_TypeChecker_Env.push_binders env bs  in
                let env = FStar_TypeChecker_Env.push_binders env ibs  in
                let t_datas =
                  FStar_List.filter
                    (fun s  ->
                       match s with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____2026,uu____2027,uu____2028,t_lid,uu____2030,uu____2031,uu____2032,uu____2033)
                           -> t_lid = lid
                       | uu____2038 -> failwith "Impossible")
                    all_datas_in_the_bundle
                   in
                let cond =
                  FStar_List.fold_left
                    (fun acc  ->
                       fun d  ->
                         let _0_311 =
                           optimized_haseq_soundness_for_data lid d usubst bs
                            in
                         FStar_Syntax_Util.mk_conj acc _0_311)
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
                let _0_313 = FStar_Syntax_Util.mk_conj guard' guard  in
                let _0_312 = FStar_Syntax_Util.mk_conj cond' cond  in
                ((FStar_List.append l_axioms [(axiom_lid, fml)]), env,
                  _0_313, _0_312)))
  
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
                  (uu____2106,us,uu____2108,uu____2109,uu____2110,uu____2111,uu____2112,uu____2113)
                  -> us
              | uu____2120 -> failwith "Impossible!"  in
            let uu____2121 = FStar_Syntax_Subst.univ_var_opening us  in
            match uu____2121 with
            | (usubst,us) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                   in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env = FStar_TypeChecker_Env.push_univ_vars env us  in
                  let uu____2137 =
                    FStar_List.fold_left (optimized_haseq_ty datas usubst us)
                      ([], env, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs
                     in
                  match uu____2137 with
                  | (axioms,env,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond  in
                      let uu____2169 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env phi  in
                      (match uu____2169 with
                       | (phi,uu____2174) ->
                           ((let uu____2176 =
                               FStar_TypeChecker_Env.should_verify env  in
                             if uu____2176
                             then
                               let _0_314 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi)
                                  in
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 _0_314
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____2184  ->
                                      match uu____2184 with
                                      | (lid,fml) ->
                                          let se =
                                            tc_assume env lid fml []
                                              FStar_Range.dummyRange
                                             in
                                          FStar_List.append l [se]) [] axioms
                                in
                             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
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
                let uu____2227 =
                  (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
                match uu____2227 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____2235) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____2262 = is_mutual t'  in
                    if uu____2262
                    then true
                    else exists_mutual (FStar_List.map Prims.fst args)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____2273) -> is_mutual t'
                | uu____2278 -> false
              
              and exists_mutual uu___80_2279 =
                match uu___80_2279 with
                | [] -> false
                | hd::tl -> (is_mutual hd) || (exists_mutual tl)
               in
              let dt = datacon_typ data  in
              let dt = FStar_Syntax_Subst.subst usubst dt  in
              let uu____2296 =
                (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n  in
              match uu____2296 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2300) ->
                  let dbs =
                    Prims.snd (FStar_List.splitAt (FStar_List.length bs) dbs)
                     in
                  let dbs =
                    let _0_315 = FStar_Syntax_Subst.opening_of_binders bs  in
                    FStar_Syntax_Subst.subst_binders _0_315 dbs  in
                  let dbs = FStar_Syntax_Subst.open_binders dbs  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             (let _0_317 =
                                let _0_316 =
                                  FStar_Syntax_Syntax.as_arg
                                    (Prims.fst b).FStar_Syntax_Syntax.sort
                                   in
                                [_0_316]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.t_haseq _0_317) None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort =
                             let uu____2343 = is_mutual sort  in
                             if uu____2343
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort  in
                           FStar_Syntax_Util.mk_conj t haseq_sort)
                      FStar_Syntax_Util.t_true dbs
                     in
                  let cond =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           (let _0_320 =
                              let _0_319 =
                                FStar_Syntax_Syntax.as_arg
                                  (let _0_318 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((Prims.fst b), None)] _0_318 None)
                                 in
                              [_0_319]  in
                            FStar_Syntax_Syntax.mk_Tm_app
                              FStar_Syntax_Util.tforall _0_320) None
                             FStar_Range.dummyRange) dbs cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond
              | uu____2366 -> acc
  
let unoptimized_haseq_ty all_datas_in_the_bundle mutuals usubst us acc ty =
  let uu____2409 =
    match ty with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2421,bs,t,uu____2424,d_lids,uu____2426,uu____2427) ->
        (lid, bs, t, d_lids)
    | uu____2435 -> failwith "Impossible!"  in
  match uu____2409 with
  | (lid,bs,t,d_lids) ->
      let bs = FStar_Syntax_Subst.subst_binders usubst bs  in
      let t =
        let _0_321 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst  in
        FStar_Syntax_Subst.subst _0_321 t  in
      let uu____2456 = FStar_Syntax_Subst.open_term bs t  in
      (match uu____2456 with
       | (bs,t) ->
           let ibs =
             let uu____2467 =
               (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
             match uu____2467 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2472) -> ibs
             | uu____2483 -> []  in
           let ibs = FStar_Syntax_Subst.open_binders ibs  in
           let ind =
             let _0_323 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let _0_322 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us  in
             FStar_Syntax_Syntax.mk_Tm_uinst _0_323 _0_322  in
           let ind =
             (let _0_325 =
                FStar_List.map
                  (fun uu____2500  ->
                     match uu____2500 with
                     | (bv,aq) ->
                         let _0_324 = FStar_Syntax_Syntax.bv_to_name bv  in
                         (_0_324, aq)) bs
                 in
              FStar_Syntax_Syntax.mk_Tm_app ind _0_325) None
               FStar_Range.dummyRange
              in
           let ind =
             (let _0_327 =
                FStar_List.map
                  (fun uu____2518  ->
                     match uu____2518 with
                     | (bv,aq) ->
                         let _0_326 = FStar_Syntax_Syntax.bv_to_name bv  in
                         (_0_326, aq)) ibs
                 in
              FStar_Syntax_Syntax.mk_Tm_app ind _0_327) None
               FStar_Range.dummyRange
              in
           let haseq_ind =
             (let _0_329 =
                let _0_328 = FStar_Syntax_Syntax.as_arg ind  in [_0_328]  in
              FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_329)
               None FStar_Range.dummyRange
              in
           let t_datas =
             FStar_List.filter
               (fun s  ->
                  match s with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____2535,uu____2536,uu____2537,t_lid,uu____2539,uu____2540,uu____2541,uu____2542)
                      -> t_lid = lid
                  | uu____2547 -> failwith "Impossible")
               all_datas_in_the_bundle
              in
           let data_cond =
             FStar_List.fold_left
               (unoptimized_haseq_data usubst bs haseq_ind mutuals)
               FStar_Syntax_Util.t_true t_datas
              in
           let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind  in
           let fml =
             let uu___85_2553 = fml  in
             let _0_333 =
               FStar_Syntax_Syntax.Tm_meta
                 (let _0_332 =
                    FStar_Syntax_Syntax.Meta_pattern
                      (let _0_331 =
                         let _0_330 = FStar_Syntax_Syntax.as_arg haseq_ind
                            in
                         [_0_330]  in
                       [_0_331])
                     in
                  (fml, _0_332))
                in
             {
               FStar_Syntax_Syntax.n = _0_333;
               FStar_Syntax_Syntax.tk = (uu___85_2553.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___85_2553.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___85_2553.FStar_Syntax_Syntax.vars)
             }  in
           let fml =
             FStar_List.fold_right
               (fun b  ->
                  fun t  ->
                    (let _0_336 =
                       let _0_335 =
                         FStar_Syntax_Syntax.as_arg
                           (let _0_334 = FStar_Syntax_Subst.close [b] t  in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              _0_334 None)
                          in
                       [_0_335]  in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                       _0_336) None FStar_Range.dummyRange) ibs fml
              in
           let fml =
             FStar_List.fold_right
               (fun b  ->
                  fun t  ->
                    (let _0_339 =
                       let _0_338 =
                         FStar_Syntax_Syntax.as_arg
                           (let _0_337 = FStar_Syntax_Subst.close [b] t  in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              _0_337 None)
                          in
                       [_0_338]  in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                       _0_339) None FStar_Range.dummyRange) bs fml
              in
           FStar_Syntax_Util.mk_conj acc fml)
  
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
                       (lid,uu____2654,uu____2655,uu____2656,uu____2657,uu____2658,uu____2659,uu____2660)
                       -> lid
                   | uu____2667 -> failwith "Impossible!") tcs
               in
            let uu____2668 =
              let ty = FStar_List.hd tcs  in
              match ty with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____2676,uu____2677,uu____2678,uu____2679,uu____2680,uu____2681)
                  -> (lid, us)
              | uu____2688 -> failwith "Impossible!"  in
            match uu____2668 with
            | (lid,us) ->
                let uu____2694 = FStar_Syntax_Subst.univ_var_opening us  in
                (match uu____2694 with
                 | (usubst,us) ->
                     let fml =
                       FStar_List.fold_left
                         (unoptimized_haseq_ty datas mutuals usubst us)
                         FStar_Syntax_Util.t_true tcs
                        in
                     let env =
                       FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
                     ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                        "haseq";
                      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                        env sig_bndle;
                      (let env = FStar_TypeChecker_Env.push_univ_vars env us
                          in
                       let se =
                         let _0_340 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")])
                            in
                         tc_assume env _0_340 fml [] FStar_Range.dummyRange
                          in
                       (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
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
          let uu____2741 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___81_2751  ->
                    match uu___81_2751 with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2752 ->
                        true
                    | uu____2764 -> false))
             in
          match uu____2741 with
          | (tys,datas) ->
              ((let uu____2777 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___82_2779  ->
                          match uu___82_2779 with
                          | FStar_Syntax_Syntax.Sig_datacon uu____2780 ->
                              false
                          | uu____2791 -> true))
                   in
                if uu____2777
                then
                  Prims.raise
                    (FStar_Errors.Error
                       (let _0_341 = FStar_TypeChecker_Env.get_range env  in
                        ("Mutually defined type contains a non-inductive element",
                          _0_341)))
                else ());
               (let env0 = env  in
                let uu____2794 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____2808  ->
                         match uu____2808 with
                         | (env,all_tcs,g) ->
                             let uu____2830 = tc_tycon env tc  in
                             (match uu____2830 with
                              | (env,tc,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u
                                     in
                                  ((let uu____2847 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Low
                                       in
                                    if uu____2847
                                    then
                                      let _0_342 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc
                                         in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" _0_342
                                    else ());
                                   (let _0_344 =
                                      let _0_343 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g'
                                         in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        _0_343
                                       in
                                    (env, ((tc, tc_u) :: all_tcs), _0_344)))))
                    tys (env, [], FStar_TypeChecker_Rel.trivial_guard)
                   in
                match uu____2794 with
                | (env,tcs,g) ->
                    let uu____2873 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____2881  ->
                             match uu____2881 with
                             | (datas,g) ->
                                 let uu____2892 = (tc_data env tcs) se  in
                                 (match uu____2892 with
                                  | (data,g') ->
                                      let _0_345 =
                                        FStar_TypeChecker_Rel.conj_guard g g'
                                         in
                                      ((data :: datas), _0_345))) datas
                        ([], g)
                       in
                    (match uu____2873 with
                     | (datas,g) ->
                         let uu____2911 =
                           generalize_and_inst_within env0 g tcs datas  in
                         (match uu____2911 with
                          | (tcs,datas) ->
                              let sig_bndle =
                                FStar_Syntax_Syntax.Sig_bundle
                                  (let _0_346 =
                                     FStar_TypeChecker_Env.get_range env0  in
                                   ((FStar_List.append tcs datas), quals,
                                     lids, _0_346))
                                 in
                              (sig_bndle, tcs, datas)))))
  