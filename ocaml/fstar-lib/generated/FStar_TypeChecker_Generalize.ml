open Prims
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Compiler_Util.set -> Prims.string)
  =
  fun univs ->
    let uu___ =
      let uu___1 = FStar_Compiler_Util.set_elements univs in
      FStar_Compiler_Effect.op_Bar_Greater uu___1
        (FStar_Compiler_List.map
           (fun u ->
              let uu___2 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_Compiler_Effect.op_Bar_Greater uu___2
                FStar_Compiler_Util.string_of_int)) in
    FStar_Compiler_Effect.op_Bar_Greater uu___ (FStar_String.concat ", ")
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Compiler_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env ->
    fun x ->
      let uu___ = FStar_Compiler_Util.set_is_empty x in
      if uu___
      then []
      else
        (let s =
           let uu___2 =
             let uu___3 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Compiler_Util.set_difference x uu___3 in
           FStar_Compiler_Effect.op_Bar_Greater uu___2
             FStar_Compiler_Util.set_elements in
         (let uu___3 =
            FStar_Compiler_Effect.op_Less_Bar
              (FStar_TypeChecker_Env.debug env) (FStar_Options.Other "Gen") in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu___5 in
            FStar_Compiler_Util.print1 "univ_vars in env: %s\n" uu___4
          else ());
         (let r =
            let uu___3 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu___3 in
          let u_names =
            FStar_Compiler_Effect.op_Bar_Greater s
              (FStar_Compiler_List.map
                 (fun u ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu___4 =
                       FStar_Compiler_Effect.op_Less_Bar
                         (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu___4
                     then
                       let uu___5 =
                         let uu___6 = FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_Compiler_Effect.op_Less_Bar
                           FStar_Compiler_Util.string_of_int uu___6 in
                       let uu___6 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu___7 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Compiler_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu___5 uu___6 uu___7
                     else ());
                    FStar_Syntax_Unionfind.univ_change u
                      (FStar_Syntax_Syntax.U_name u_name);
                    u_name)) in
          u_names))
let (gather_free_univnames :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.univ_name FStar_Compiler_Util.set)
  =
  fun env ->
    fun t ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env in
      let tm_univnames = FStar_Syntax_Free.univnames t in
      let univnames =
        FStar_Compiler_Util.set_difference tm_univnames ctx_univnames in
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
        | ([], uu___) -> generalized_univ_names
        | (uu___, []) -> explicit_univ_names
        | uu___ ->
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Syntax_Print.term_to_string t in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu___3 in
              (FStar_Errors_Codes.Fatal_UnexpectedGeneralizedUniverse,
                uu___2) in
            FStar_Errors.raise_error uu___1 t.FStar_Syntax_Syntax.pos
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun t0 ->
      FStar_Errors.with_ctx "While generalizing universes"
        (fun uu___ ->
           let t =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Env.NoFullNorm;
               FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.DoNotUnfoldPureLets] env t0 in
           let univnames =
             let uu___1 = gather_free_univnames env t in
             FStar_Compiler_Util.set_elements uu___1 in
           (let uu___2 =
              FStar_Compiler_Effect.op_Less_Bar
                (FStar_TypeChecker_Env.debug env) (FStar_Options.Other "Gen") in
            if uu___2
            then
              let uu___3 = FStar_Syntax_Print.term_to_string t in
              let uu___4 = FStar_Syntax_Print.univ_names_to_string univnames in
              FStar_Compiler_Util.print2
                "generalizing universes in the term (post norm): %s with univnames: %s\n"
                uu___3 uu___4
            else ());
           (let univs = FStar_Syntax_Free.univs t in
            (let uu___3 =
               FStar_Compiler_Effect.op_Less_Bar
                 (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Gen") in
             if uu___3
             then
               let uu___4 = string_of_univs univs in
               FStar_Compiler_Util.print1 "univs to gen : %s\n" uu___4
             else ());
            (let gen = gen_univs env univs in
             (let uu___4 =
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Gen") in
              if uu___4
              then
                let uu___5 = FStar_Syntax_Print.term_to_string t in
                let uu___6 = FStar_Syntax_Print.univ_names_to_string gen in
                FStar_Compiler_Util.print2
                  "After generalization, t: %s and univs: %s\n" uu___5 uu___6
              else ());
             (let univs1 = check_universe_generalization univnames gen t0 in
              let t1 =
                FStar_TypeChecker_Normalize.reduce_uvar_solutions env t in
              let ts = FStar_Syntax_Subst.close_univ_vars univs1 t1 in
              (univs1, ts)))))
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
        let uu___ =
          let uu___1 =
            FStar_Compiler_Util.for_all
              (fun uu___2 ->
                 match uu___2 with
                 | (uu___3, uu___4, c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_Compiler_Effect.op_Less_Bar Prims.op_Negation uu___1 in
        if uu___
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu___3 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu___3
              then
                let uu___4 = FStar_Syntax_Print.comp_to_string c in
                FStar_Compiler_Util.print1
                  "Normalizing before generalizing:\n\t %s\n" uu___4
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c in
              (let uu___4 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu___4
               then
                 let uu___5 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Compiler_Util.print1 "Normalized to:\n\t %s\n" uu___5
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu___2 = FStar_Compiler_Util.set_difference uvs env_uvars in
             FStar_Compiler_Effect.op_Bar_Greater uu___2
               FStar_Compiler_Util.set_elements in
           let univs_and_uvars_of_lec uu___2 =
             match uu___2 with
             | (lbname, e, c) ->
                 let c1 = norm c in
                 let t = FStar_Syntax_Util.comp_result c1 in
                 let univs = FStar_Syntax_Free.univs t in
                 let uvt = FStar_Syntax_Free.uvars t in
                 ((let uu___4 =
                     FStar_Compiler_Effect.op_Less_Bar
                       (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu___4
                   then
                     let uu___5 =
                       let uu___6 =
                         let uu___7 = FStar_Compiler_Util.set_elements univs in
                         FStar_Compiler_Effect.op_Bar_Greater uu___7
                           (FStar_Compiler_List.map
                              (fun u ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_Compiler_Effect.op_Bar_Greater uu___6
                         (FStar_String.concat ", ") in
                     let uu___6 =
                       let uu___7 =
                         let uu___8 = FStar_Compiler_Util.set_elements uvt in
                         FStar_Compiler_Effect.op_Bar_Greater uu___8
                           (FStar_Compiler_List.map
                              (fun u ->
                                 let uu___9 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head in
                                 let uu___10 =
                                   let uu___11 =
                                     FStar_Syntax_Util.ctx_uvar_typ u in
                                   FStar_Syntax_Print.term_to_string uu___11 in
                                 FStar_Compiler_Util.format2 "(%s : %s)"
                                   uu___9 uu___10)) in
                       FStar_Compiler_Effect.op_Bar_Greater uu___7
                         (FStar_String.concat ", ") in
                     FStar_Compiler_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu___5
                       uu___6
                   else ());
                  (let univs1 =
                     let uu___4 = FStar_Compiler_Util.set_elements uvt in
                     FStar_Compiler_List.fold_left
                       (fun univs2 ->
                          fun uv ->
                            let uu___5 =
                              let uu___6 = FStar_Syntax_Util.ctx_uvar_typ uv in
                              FStar_Syntax_Free.univs uu___6 in
                            FStar_Compiler_Util.set_union univs2 uu___5)
                       univs uu___4 in
                   let uvs = gen_uvars uvt in
                   (let uu___5 =
                      FStar_Compiler_Effect.op_Less_Bar
                        (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu___5
                    then
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            FStar_Compiler_Util.set_elements univs1 in
                          FStar_Compiler_Effect.op_Bar_Greater uu___8
                            (FStar_Compiler_List.map
                               (fun u ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_Compiler_Effect.op_Bar_Greater uu___7
                          (FStar_String.concat ", ") in
                      let uu___7 =
                        let uu___8 =
                          FStar_Compiler_Effect.op_Bar_Greater uvs
                            (FStar_Compiler_List.map
                               (fun u ->
                                  let uu___9 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head in
                                  let uu___10 =
                                    let uu___11 =
                                      FStar_Syntax_Util.ctx_uvar_typ u in
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env uu___11 in
                                  FStar_Compiler_Util.format2 "(%s : %s)"
                                    uu___9 uu___10)) in
                        FStar_Compiler_Effect.op_Bar_Greater uu___8
                          (FStar_String.concat ", ") in
                      FStar_Compiler_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu___6
                        uu___7
                    else ());
                   (univs1, uvs, (lbname, e, c1)))) in
           let uu___2 =
             let uu___3 = FStar_Compiler_List.hd lecs in
             univs_and_uvars_of_lec uu___3 in
           match uu___2 with
           | (univs, uvs, lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu___3 =
                   (FStar_Compiler_Util.set_is_subset_of u1 u2) &&
                     (FStar_Compiler_Util.set_is_subset_of u2 u1) in
                 if uu___3
                 then ()
                 else
                   (let uu___5 = lec_hd in
                    match uu___5 with
                    | (lb1, uu___6, uu___7) ->
                        let uu___8 = lec2 in
                        (match uu___8 with
                         | (lb2, uu___9, uu___10) ->
                             let msg =
                               let uu___11 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu___12 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Compiler_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu___11 uu___12 in
                             let uu___11 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors_Codes.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu___11)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_Compiler_Effect.op_Bar_Greater u11
                     (FStar_Compiler_Util.for_all
                        (fun u ->
                           FStar_Compiler_Effect.op_Bar_Greater u21
                             (FStar_Compiler_Util.for_some
                                (fun u' ->
                                   FStar_Syntax_Unionfind.equiv
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                     u'.FStar_Syntax_Syntax.ctx_uvar_head)))) in
                 let uu___3 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu___3
                 then ()
                 else
                   (let uu___5 = lec_hd in
                    match uu___5 with
                    | (lb1, uu___6, uu___7) ->
                        let uu___8 = lec2 in
                        (match uu___8 with
                         | (lb2, uu___9, uu___10) ->
                             let msg =
                               let uu___11 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu___12 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Compiler_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu___11 uu___12 in
                             let uu___11 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors_Codes.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu___11)) in
               let lecs1 =
                 let uu___3 = FStar_Compiler_List.tl lecs in
                 FStar_Compiler_List.fold_right
                   (fun this_lec ->
                      fun lecs2 ->
                        let uu___4 = univs_and_uvars_of_lec this_lec in
                        match uu___4 with
                        | (this_univs, this_uvs, this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs2)) uu___3 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu___3 = lec_hd in
                   match uu___3 with
                   | (lbname, e, c) ->
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = FStar_Syntax_Print.term_to_string k in
                           let uu___7 =
                             FStar_Syntax_Print.lbname_to_string lbname in
                           let uu___8 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c) in
                           FStar_Compiler_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu___6 uu___7 uu___8 in
                         (FStar_Errors_Codes.Fatal_FailToResolveImplicitArgument,
                           uu___5) in
                       FStar_Errors.raise_error uu___4 rng in
                 FStar_Compiler_Effect.op_Bar_Greater uvs1
                   (FStar_Compiler_List.map
                      (fun u ->
                         let uu___3 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head in
                         match uu___3 with
                         | FStar_Pervasives_Native.Some uu___4 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu___4 ->
                             let k =
                               let uu___5 = FStar_Syntax_Util.ctx_uvar_typ u in
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env uu___5 in
                             let uu___5 = FStar_Syntax_Util.arrow_formals k in
                             (match uu___5 with
                              | (bs, kres) ->
                                  ((let uu___7 =
                                      let uu___8 =
                                        let uu___9 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres in
                                        FStar_Syntax_Util.unrefine uu___9 in
                                      uu___8.FStar_Syntax_Syntax.n in
                                    match uu___7 with
                                    | FStar_Syntax_Syntax.Tm_type uu___8 ->
                                        let free =
                                          FStar_Syntax_Free.names kres in
                                        let uu___9 =
                                          let uu___10 =
                                            FStar_Compiler_Util.set_is_empty
                                              free in
                                          Prims.op_Negation uu___10 in
                                        if uu___9
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu___8 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu___7 =
                                        let uu___8 =
                                          FStar_TypeChecker_Env.get_range env in
                                        FStar_Compiler_Effect.op_Less_Bar
                                          (fun uu___9 ->
                                             FStar_Pervasives_Native.Some
                                               uu___9) uu___8 in
                                      FStar_Syntax_Syntax.new_bv uu___7 kres in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu___7 ->
                                          let uu___8 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Util.abs bs uu___8
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_tot
                                                  kres)) in
                                    FStar_Syntax_Util.set_uvar
                                      u.FStar_Syntax_Syntax.ctx_uvar_head t;
                                    (let uu___8 =
                                       FStar_Syntax_Syntax.as_bqual_implicit
                                         true in
                                     (a, uu___8))))))) in
               let gen_univs1 = gen_univs env univs in
               let gen_tvars = gen_types uvs in
               let ecs =
                 FStar_Compiler_Effect.op_Bar_Greater lecs2
                   (FStar_Compiler_List.map
                      (fun uu___3 ->
                         match uu___3 with
                         | (lbname, e, c) ->
                             let uu___4 =
                               match (gen_tvars, gen_univs1) with
                               | ([], []) -> (e, c, [])
                               | uu___5 ->
                                   let uu___6 = (e, c) in
                                   (match uu___6 with
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
                                              FStar_Compiler_List.map
                                                (fun uu___7 ->
                                                   match uu___7 with
                                                   | (x, uu___8) ->
                                                       let uu___9 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu___9) gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu___7 =
                                                let uu___8 =
                                                  FStar_Compiler_Util.right
                                                    lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu___8 in
                                              if uu___7
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1 in
                                        let tvars_bs =
                                          FStar_Compiler_Effect.op_Bar_Greater
                                            gen_tvars
                                            (FStar_Compiler_List.map
                                               (fun uu___7 ->
                                                  match uu___7 with
                                                  | (x, q) ->
                                                      FStar_Syntax_Syntax.mk_binder_with_attrs
                                                        x q
                                                        FStar_Pervasives_Native.None
                                                        [])) in
                                        let t =
                                          let uu___7 =
                                            let uu___8 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu___8.FStar_Syntax_Syntax.n in
                                          match uu___7 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs, cod) ->
                                              let uu___8 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu___8 with
                                               | (bs1, cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_Compiler_List.op_At
                                                        tvars_bs bs1) cod1)
                                          | uu___8 ->
                                              FStar_Syntax_Util.arrow
                                                tvars_bs c1 in
                                        let e' =
                                          let uu___7 =
                                            let uu___8 =
                                              FStar_Syntax_Util.residual_comp_of_comp
                                                c1 in
                                            FStar_Pervasives_Native.Some
                                              uu___8 in
                                          FStar_Syntax_Util.abs tvars_bs e2
                                            uu___7 in
                                        let uu___7 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu___7, tvars_bs)) in
                             (match uu___4 with
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
        (let uu___2 =
           FStar_Compiler_List.for_all
             (fun uu___3 ->
                match uu___3 with
                | (l, uu___4, uu___5) -> FStar_Compiler_Util.is_right l) lecs in
         ());
        (let uu___2 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu___2
         then
           let uu___3 =
             let uu___4 =
               FStar_Compiler_List.map
                 (fun uu___5 ->
                    match uu___5 with
                    | (lb, uu___6, uu___7) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_Compiler_Effect.op_Bar_Greater uu___4
               (FStar_String.concat ", ") in
           FStar_Compiler_Util.print1 "Generalizing: %s\n" uu___3
         else ());
        (let univnames_lecs =
           let empty =
             FStar_Compiler_Util.as_set []
               FStar_Syntax_Syntax.order_univ_name in
           FStar_Compiler_List.fold_left
             (fun out ->
                fun uu___2 ->
                  match uu___2 with
                  | (l, t, c) ->
                      let uu___3 = gather_free_univnames env t in
                      FStar_Compiler_Util.set_union out uu___3) empty lecs in
         let univnames_lecs1 =
           FStar_Compiler_Util.set_elements univnames_lecs in
         let generalized_lecs =
           let uu___2 = gen env is_rec lecs in
           match uu___2 with
           | FStar_Pervasives_Native.None ->
               FStar_Compiler_Effect.op_Bar_Greater lecs
                 (FStar_Compiler_List.map
                    (fun uu___3 ->
                       match uu___3 with | (l, t, c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu___4 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu___4
                 then
                   FStar_Compiler_Effect.op_Bar_Greater luecs
                     (FStar_Compiler_List.iter
                        (fun uu___5 ->
                           match uu___5 with
                           | (l, us, e, c, gvs) ->
                               let uu___6 =
                                 FStar_Compiler_Range_Ops.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu___7 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu___8 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu___9 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu___10 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Compiler_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu___6 uu___7 uu___8 uu___9 uu___10))
                 else ());
                luecs) in
         FStar_Compiler_List.map
           (fun uu___2 ->
              match uu___2 with
              | (l, generalized_univs, t, c, gvs) ->
                  let uu___3 =
                    check_universe_generalization univnames_lecs1
                      generalized_univs t in
                  (l, uu___3, t, c, gvs)) generalized_lecs)
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
        FStar_Errors.with_ctx "While generalizing"
          (fun uu___ ->
             let uu___1 =
               let uu___2 =
                 let uu___3 = FStar_TypeChecker_Env.current_module env in
                 FStar_Ident.string_of_lid uu___3 in
               FStar_Pervasives_Native.Some uu___2 in
             FStar_Profiling.profile
               (fun uu___2 -> generalize' env is_rec lecs) uu___1
               "FStar.TypeChecker.Util.generalize")