open Prims
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs ->
    let uu____9 =
      let uu____12 = FStar_Util.set_elements univs in
      FStar_All.pipe_right uu____12
        (FStar_List.map
           (fun u ->
              let uu____22 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____22 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____9 (FStar_String.concat ", ")
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env ->
    fun x ->
      let uu____43 = FStar_Util.set_is_empty x in
      if uu____43
      then []
      else
        (let s =
           let uu____60 =
             let uu____63 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____63 in
           FStar_All.pipe_right uu____60 FStar_Util.set_elements in
         (let uu____81 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____81
          then
            let uu____82 =
              let uu____83 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____83 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____82
          else ());
         (let r =
            let uu____90 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____90 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____135 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____135
                     then
                       let uu____136 =
                         let uu____137 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____137 in
                       let uu____138 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____139 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____136
                         uu____138 uu____139
                     else ());
                    FStar_Syntax_Unionfind.univ_change u
                      (FStar_Syntax_Syntax.U_name u_name);
                    u_name)) in
          u_names))
let (gather_free_univnames :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env ->
    fun t ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env in
      let tm_univnames = FStar_Syntax_Free.univnames t in
      let univnames =
        let uu____165 = FStar_Util.set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____165 FStar_Util.set_elements in
      univnames
let (check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun explicit_univ_names ->
    fun generalized_univ_names ->
      fun t ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([], uu____203) -> generalized_univ_names
        | (uu____210, []) -> explicit_univ_names
        | uu____217 ->
            let uu____226 =
              let uu____231 =
                let uu____232 = FStar_Syntax_Print.term_to_string t in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____232 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____231) in
            FStar_Errors.raise_error uu____226 t.FStar_Syntax_Syntax.pos
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun t0 ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.NoFullNorm;
          FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.DoNotUnfoldPureLets] env t0 in
      let univnames = gather_free_univnames env t in
      (let uu____250 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____250
       then
         let uu____251 = FStar_Syntax_Print.term_to_string t in
         let uu____252 = FStar_Syntax_Print.univ_names_to_string univnames in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____251 uu____252
       else ());
      (let univs = FStar_Syntax_Free.univs t in
       (let uu____258 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____258
        then
          let uu____259 = string_of_univs univs in
          FStar_Util.print1 "univs to gen : %s\n" uu____259
        else ());
       (let gen = gen_univs env univs in
        (let uu____265 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen") in
         if uu____265
         then
           let uu____266 = FStar_Syntax_Print.term_to_string t in
           let uu____267 = FStar_Syntax_Print.univ_names_to_string gen in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____266 uu____267
         else ());
        (let univs1 = check_universe_generalization univnames gen t0 in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t in
         let ts = FStar_Syntax_Subst.close_univ_vars univs1 t1 in
         (univs1, ts))))
let (gen :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_name
          Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list
          FStar_Pervasives_Native.option)
  =
  fun env ->
    fun is_rec ->
      fun lecs ->
        let uu____345 =
          let uu____346 =
            FStar_Util.for_all
              (fun uu____359 ->
                 match uu____359 with
                 | (uu____368, uu____369, c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____346 in
        if uu____345
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____417 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____417
              then
                let uu____418 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____418
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c in
              (let uu____422 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____422
               then
                 let uu____423 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____423
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____438 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____438 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____472 =
             match uu____472 with
             | (lbname, e, c) ->
                 let c1 = norm c in
                 let t = FStar_Syntax_Util.comp_result c1 in
                 let univs = FStar_Syntax_Free.univs t in
                 let uvt = FStar_Syntax_Free.uvars t in
                 ((let uu____509 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____509
                   then
                     let uu____510 =
                       let uu____511 =
                         let uu____514 = FStar_Util.set_elements univs in
                         FStar_All.pipe_right uu____514
                           (FStar_List.map
                              (fun u ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____511
                         (FStar_String.concat ", ") in
                     let uu____565 =
                       let uu____566 =
                         let uu____569 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____569
                           (FStar_List.map
                              (fun u ->
                                 let uu____580 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head in
                                 let uu____581 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                 FStar_Util.format2 "(%s : %s)" uu____580
                                   uu____581)) in
                       FStar_All.pipe_right uu____566
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____510
                       uu____565
                   else ());
                  (let univs1 =
                     let uu____588 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs1 ->
                          fun uv ->
                            let uu____600 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                            FStar_Util.set_union univs1 uu____600) univs
                       uu____588 in
                   let uvs = gen_uvars uvt in
                   (let uu____607 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____607
                    then
                      let uu____608 =
                        let uu____609 =
                          let uu____612 = FStar_Util.set_elements univs1 in
                          FStar_All.pipe_right uu____612
                            (FStar_List.map
                               (fun u ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____609
                          (FStar_String.concat ", ") in
                      let uu____663 =
                        let uu____664 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u ->
                                  let uu____675 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head in
                                  let uu____676 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                  FStar_Util.format2 "(%s : %s)" uu____675
                                    uu____676)) in
                        FStar_All.pipe_right uu____664
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____608
                        uu____663
                    else ());
                   (univs1, uvs, (lbname, e, c1)))) in
           let uu____690 =
             let uu____707 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____707 in
           match uu____690 with
           | (univs, uvs, lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____797 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____797
                 then ()
                 else
                   (let uu____799 = lec_hd in
                    match uu____799 with
                    | (lb1, uu____807, uu____808) ->
                        let uu____809 = lec2 in
                        (match uu____809 with
                         | (lb2, uu____817, uu____818) ->
                             let msg =
                               let uu____820 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____821 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____820 uu____821 in
                             let uu____822 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____822)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun u ->
                           FStar_All.pipe_right u21
                             (FStar_Util.for_some
                                (fun u' ->
                                   FStar_Syntax_Unionfind.equiv
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                     u'.FStar_Syntax_Syntax.ctx_uvar_head)))) in
                 let uu____886 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____886
                 then ()
                 else
                   (let uu____888 = lec_hd in
                    match uu____888 with
                    | (lb1, uu____896, uu____897) ->
                        let uu____898 = lec2 in
                        (match uu____898 with
                         | (lb2, uu____906, uu____907) ->
                             let msg =
                               let uu____909 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____910 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____909 uu____910 in
                             let uu____911 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____911)) in
               let lecs1 =
                 let uu____921 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec ->
                      fun lecs1 ->
                        let uu____974 = univs_and_uvars_of_lec this_lec in
                        match uu____974 with
                        | (this_univs, this_uvs, this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____921 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____1084 = lec_hd in
                   match uu____1084 with
                   | (lbname, e, c) ->
                       let uu____1094 =
                         let uu____1099 =
                           let uu____1100 =
                             FStar_Syntax_Print.term_to_string k in
                           let uu____1101 =
                             FStar_Syntax_Print.lbname_to_string lbname in
                           let uu____1102 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c) in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____1100 uu____1101 uu____1102 in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____1099) in
                       FStar_Errors.raise_error uu____1094 rng in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u ->
                         let uu____1121 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head in
                         match uu____1121 with
                         | FStar_Pervasives_Native.Some uu____1130 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____1137 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ in
                             let uu____1141 =
                               FStar_Syntax_Util.arrow_formals k in
                             (match uu____1141 with
                              | (bs, kres) ->
                                  ((let uu____1161 =
                                      let uu____1162 =
                                        let uu____1165 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres in
                                        FStar_Syntax_Util.unrefine uu____1165 in
                                      uu____1162.FStar_Syntax_Syntax.n in
                                    match uu____1161 with
                                    | FStar_Syntax_Syntax.Tm_type uu____1166
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres in
                                        let uu____1170 =
                                          let uu____1171 =
                                            FStar_Util.set_is_empty free in
                                          Prims.op_Negation uu____1171 in
                                        if uu____1170
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____1173 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____1175 =
                                        let uu____1178 =
                                          FStar_TypeChecker_Env.get_range env in
                                        FStar_All.pipe_left
                                          (fun uu____1181 ->
                                             FStar_Pervasives_Native.Some
                                               uu____1181) uu____1178 in
                                      FStar_Syntax_Syntax.new_bv uu____1175
                                        kres in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____1189 ->
                                          let uu____1190 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Util.abs bs uu____1190
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_tot
                                                  kres)) in
                                    FStar_Syntax_Util.set_uvar
                                      u.FStar_Syntax_Syntax.ctx_uvar_head t;
                                    (a,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))))) in
               let gen_univs1 = gen_univs env univs in
               let gen_tvars = gen_types uvs in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____1293 ->
                         match uu____1293 with
                         | (lbname, e, c) ->
                             let uu____1339 =
                               match (gen_tvars, gen_univs1) with
                               | ([], []) -> (e, c, [])
                               | uu____1400 ->
                                   let uu____1413 = (e, c) in
                                   (match uu____1413 with
                                    | (e0, c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Env.Beta;
                                            FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                                            FStar_TypeChecker_Env.CompressUvars;
                                            FStar_TypeChecker_Env.NoFullNorm;
                                            FStar_TypeChecker_Env.Exclude
                                              FStar_TypeChecker_Env.Zeta] env
                                            c in
                                        let e1 =
                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                            env e in
                                        let e2 =
                                          if is_rec
                                          then
                                            let tvar_args =
                                              FStar_List.map
                                                (fun uu____1452 ->
                                                   match uu____1452 with
                                                   | (x, uu____1458) ->
                                                       let uu____1459 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____1459)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____1477 =
                                                let uu____1478 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____1478 in
                                              if uu____1477
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1 in
                                        let t =
                                          let uu____1484 =
                                            let uu____1485 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____1485.FStar_Syntax_Syntax.n in
                                          match uu____1484 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs, cod) ->
                                              let uu____1510 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____1510 with
                                               | (bs1, cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____1521 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____1525 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____1525, gen_tvars)) in
                             (match uu____1339 with
                              | (e1, c1, gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs)))) in
               FStar_Pervasives_Native.Some ecs)
let (generalize' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list)
  =
  fun env ->
    fun is_rec ->
      fun lecs ->
        (let uu____1669 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____1669
         then
           let uu____1670 =
             let uu____1671 =
               FStar_List.map
                 (fun uu____1684 ->
                    match uu____1684 with
                    | (lb, uu____1692, uu____1693) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____1671 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____1670
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____1714 ->
                match uu____1714 with
                | (l, t, c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____1743 = gen env is_rec lecs in
           match uu____1743 with
           | FStar_Pervasives_Native.None ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____1842 ->
                       match uu____1842 with | (l, t, c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____1904 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____1904
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____1950 ->
                           match uu____1950 with
                           | (l, us, e, c, gvs) ->
                               let uu____1984 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____1985 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____1986 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____1987 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____1988 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____1984 uu____1985 uu____1986 uu____1987
                                 uu____1988))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames ->
              fun uu____2029 ->
                match uu____2029 with
                | (l, generalized_univs, t, c, gvs) ->
                    let uu____2073 =
                      check_universe_generalization univnames
                        generalized_univs t in
                    (l, uu____2073, t, c, gvs)) univnames_lecs
           generalized_lecs)
let (generalize :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list)
  =
  fun env ->
    fun is_rec ->
      fun lecs ->
        let uu____2125 =
          let uu____2128 =
            let uu____2129 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu____2129 in
          FStar_Pervasives_Native.Some uu____2128 in
        FStar_Profiling.profile
          (fun uu____2145 -> generalize' env is_rec lecs) uu____2125
          "FStar.TypeChecker.Util.generalize"