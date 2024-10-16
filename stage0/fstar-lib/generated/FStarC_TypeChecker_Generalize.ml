open Prims
let (dbg_Gen : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Gen"
let (showable_univ_var :
  FStarC_Syntax_Syntax.universe_uvar FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun u ->
         FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
           (FStarC_Syntax_Syntax.U_unif u))
  }
let (gen_univs :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.universe_uvar FStarC_Compiler_FlatSet.t ->
      FStarC_Syntax_Syntax.univ_name Prims.list)
  =
  fun env ->
    fun x ->
      let uu___ =
        FStarC_Class_Setlike.is_empty ()
          (Obj.magic
             (FStarC_Compiler_FlatSet.setlike_flat_set
                FStarC_Syntax_Free.ord_univ_uvar)) (Obj.magic x) in
      if uu___
      then []
      else
        (let s =
           let uu___2 =
             let uu___3 = FStarC_TypeChecker_Env.univ_vars env in
             Obj.magic
               (FStarC_Class_Setlike.diff ()
                  (Obj.magic
                     (FStarC_Compiler_FlatSet.setlike_flat_set
                        FStarC_Syntax_Free.ord_univ_uvar)) (Obj.magic x)
                  (Obj.magic uu___3)) in
           FStarC_Class_Setlike.elems ()
             (Obj.magic
                (FStarC_Compiler_FlatSet.setlike_flat_set
                   FStarC_Syntax_Free.ord_univ_uvar)) (Obj.magic uu___2) in
         (let uu___3 = FStarC_Compiler_Effect.op_Bang dbg_Gen in
          if uu___3
          then
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_Env.univ_vars env in
              FStarC_Class_Show.show
                (FStarC_Compiler_FlatSet.showable_set
                   FStarC_Syntax_Free.ord_univ_uvar showable_univ_var) uu___5 in
            FStarC_Compiler_Util.print1 "univ_vars in env: %s\n" uu___4
          else ());
         (let r =
            let uu___3 = FStarC_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu___3 in
          let u_names =
            FStarC_Compiler_List.map
              (fun u ->
                 let u_name = FStarC_Syntax_Syntax.new_univ_name r in
                 (let uu___4 = FStarC_Compiler_Effect.op_Bang dbg_Gen in
                  if uu___4
                  then
                    let uu___5 =
                      let uu___6 = FStarC_Syntax_Unionfind.univ_uvar_id u in
                      FStarC_Compiler_Util.string_of_int uu___6 in
                    let uu___6 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_univ
                        (FStarC_Syntax_Syntax.U_unif u) in
                    let uu___7 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_univ
                        (FStarC_Syntax_Syntax.U_name u_name) in
                    FStarC_Compiler_Util.print3 "Setting ?%s (%s) to %s\n"
                      uu___5 uu___6 uu___7
                  else ());
                 FStarC_Syntax_Unionfind.univ_change u
                   (FStarC_Syntax_Syntax.U_name u_name);
                 u_name) s in
          u_names))
let (gather_free_univnames :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.univ_name FStarC_Compiler_FlatSet.t)
  =
  fun env ->
    fun t ->
      let ctx_univnames = FStarC_TypeChecker_Env.univnames env in
      let tm_univnames = FStarC_Syntax_Free.univnames t in
      let univnames =
        Obj.magic
          (FStarC_Class_Setlike.diff ()
             (Obj.magic
                (FStarC_Compiler_FlatSet.setlike_flat_set
                   FStarC_Syntax_Syntax.ord_ident)) (Obj.magic tm_univnames)
             (Obj.magic ctx_univnames)) in
      univnames
let (check_universe_generalization :
  FStarC_Syntax_Syntax.univ_name Prims.list ->
    FStarC_Syntax_Syntax.univ_name Prims.list ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.univ_name Prims.list)
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
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
              Prims.strcat
                "Generalized universe in a term containing explicit universe annotation : "
                uu___2 in
            FStarC_Errors.raise_error
              (FStarC_Syntax_Syntax.has_range_syntax ()) t
              FStarC_Errors_Codes.Fatal_UnexpectedGeneralizedUniverse ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___1)
let (generalize_universes :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun t0 ->
      FStarC_Errors.with_ctx "While generalizing universes"
        (fun uu___ ->
           let t =
             FStarC_TypeChecker_Normalize.normalize
               [FStarC_TypeChecker_Env.NoFullNorm;
               FStarC_TypeChecker_Env.Beta;
               FStarC_TypeChecker_Env.DoNotUnfoldPureLets] env t0 in
           let univnames =
             let uu___1 = gather_free_univnames env t in
             FStarC_Class_Setlike.elems ()
               (Obj.magic
                  (FStarC_Compiler_FlatSet.setlike_flat_set
                     FStarC_Syntax_Syntax.ord_ident)) (Obj.magic uu___1) in
           (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_Gen in
            if uu___2
            then
              let uu___3 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
              let uu___4 =
                FStarC_Class_Show.show
                  (FStarC_Class_Show.show_list FStarC_Ident.showable_ident)
                  univnames in
              FStarC_Compiler_Util.print2
                "generalizing universes in the term (post norm): %s with univnames: %s\n"
                uu___3 uu___4
            else ());
           (let univs = FStarC_Syntax_Free.univs t in
            (let uu___3 = FStarC_Compiler_Effect.op_Bang dbg_Gen in
             if uu___3
             then
               let uu___4 =
                 FStarC_Class_Show.show
                   (FStarC_Compiler_FlatSet.showable_set
                      FStarC_Syntax_Free.ord_univ_uvar showable_univ_var)
                   univs in
               FStarC_Compiler_Util.print1 "univs to gen : %s\n" uu___4
             else ());
            (let gen = gen_univs env univs in
             (let uu___4 = FStarC_Compiler_Effect.op_Bang dbg_Gen in
              if uu___4
              then
                let uu___5 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
                let uu___6 =
                  FStarC_Class_Show.show
                    (FStarC_Class_Show.show_list FStarC_Ident.showable_ident)
                    gen in
                FStarC_Compiler_Util.print2
                  "After generalization, t: %s and univs: %s\n" uu___5 uu___6
              else ());
             (let univs1 = check_universe_generalization univnames gen t0 in
              let t1 =
                FStarC_TypeChecker_Normalize.reduce_uvar_solutions env t in
              let ts = FStarC_Syntax_Subst.close_univ_vars univs1 t1 in
              (univs1, ts)))))
let (gen :
  FStarC_TypeChecker_Env.env ->
    Prims.bool ->
      (FStarC_Syntax_Syntax.lbname * FStarC_Syntax_Syntax.term *
        FStarC_Syntax_Syntax.comp) Prims.list ->
        (FStarC_Syntax_Syntax.lbname * FStarC_Syntax_Syntax.univ_name
          Prims.list * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.comp
          * FStarC_Syntax_Syntax.binder Prims.list) Prims.list
          FStar_Pervasives_Native.option)
  =
  fun env ->
    fun is_rec ->
      fun lecs ->
        let uu___ =
          let uu___1 =
            FStarC_Compiler_Util.for_all
              (fun uu___2 ->
                 match uu___2 with
                 | (uu___3, uu___4, c) ->
                     FStarC_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          Prims.op_Negation uu___1 in
        if uu___
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu___3 = FStarC_Compiler_Debug.medium () in
              if uu___3
              then
                let uu___4 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp c in
                FStarC_Compiler_Util.print1
                  "Normalizing before generalizing:\n\t %s\n" uu___4
              else ());
             (let c1 =
                FStarC_TypeChecker_Normalize.normalize_comp
                  [FStarC_TypeChecker_Env.Beta;
                  FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta;
                  FStarC_TypeChecker_Env.NoFullNorm;
                  FStarC_TypeChecker_Env.DoNotUnfoldPureLets] env c in
              (let uu___4 = FStarC_Compiler_Debug.medium () in
               if uu___4
               then
                 let uu___5 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp
                     c1 in
                 FStarC_Compiler_Util.print1 "Normalized to:\n\t %s\n" uu___5
               else ());
              c1) in
           let env_uvars = FStarC_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu___2 =
               Obj.magic
                 (FStarC_Class_Setlike.diff ()
                    (Obj.magic
                       (FStarC_Compiler_FlatSet.setlike_flat_set
                          FStarC_Syntax_Free.ord_ctx_uvar)) (Obj.magic uvs)
                    (Obj.magic env_uvars)) in
             FStarC_Class_Setlike.elems ()
               (Obj.magic
                  (FStarC_Compiler_FlatSet.setlike_flat_set
                     FStarC_Syntax_Free.ord_ctx_uvar)) (Obj.magic uu___2) in
           let univs_and_uvars_of_lec uu___2 =
             match uu___2 with
             | (lbname, e, c) ->
                 let c1 = norm c in
                 let t = FStarC_Syntax_Util.comp_result c1 in
                 let univs = FStarC_Syntax_Free.univs t in
                 let uvt = FStarC_Syntax_Free.uvars t in
                 ((let uu___4 = FStarC_Compiler_Effect.op_Bang dbg_Gen in
                   if uu___4
                   then
                     let uu___5 =
                       FStarC_Class_Show.show
                         (FStarC_Compiler_FlatSet.showable_set
                            FStarC_Syntax_Free.ord_univ_uvar
                            showable_univ_var) univs in
                     let uu___6 =
                       FStarC_Class_Show.show
                         (FStarC_Compiler_FlatSet.showable_set
                            FStarC_Syntax_Free.ord_ctx_uvar
                            FStarC_Syntax_Print.showable_ctxu) uvt in
                     FStarC_Compiler_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu___5
                       uu___6
                   else ());
                  (let univs1 =
                     let uu___4 =
                       FStarC_Class_Setlike.elems ()
                         (Obj.magic
                            (FStarC_Compiler_FlatSet.setlike_flat_set
                               FStarC_Syntax_Free.ord_ctx_uvar))
                         (Obj.magic uvt) in
                     FStarC_Compiler_List.fold_left
                       (fun uu___6 ->
                          fun uu___5 ->
                            (fun univs2 ->
                               fun uv ->
                                 let uu___5 =
                                   let uu___6 =
                                     FStarC_Syntax_Util.ctx_uvar_typ uv in
                                   FStarC_Syntax_Free.univs uu___6 in
                                 Obj.magic
                                   (FStarC_Class_Setlike.union ()
                                      (Obj.magic
                                         (FStarC_Compiler_FlatSet.setlike_flat_set
                                            FStarC_Syntax_Free.ord_univ_uvar))
                                      (Obj.magic univs2) (Obj.magic uu___5)))
                              uu___6 uu___5) univs uu___4 in
                   let uvs = gen_uvars uvt in
                   (let uu___5 = FStarC_Compiler_Effect.op_Bang dbg_Gen in
                    if uu___5
                    then
                      let uu___6 =
                        FStarC_Class_Show.show
                          (FStarC_Compiler_FlatSet.showable_set
                             FStarC_Syntax_Free.ord_univ_uvar
                             showable_univ_var) univs1 in
                      let uu___7 =
                        FStarC_Class_Show.show
                          (FStarC_Class_Show.show_list
                             FStarC_Syntax_Print.showable_ctxu) uvs in
                      FStarC_Compiler_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars = %s\n" uu___6
                        uu___7
                    else ());
                   (univs1, uvs, (lbname, e, c1)))) in
           let uu___2 =
             let uu___3 = FStarC_Compiler_List.hd lecs in
             univs_and_uvars_of_lec uu___3 in
           match uu___2 with
           | (univs, uvs, lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu___3 =
                   FStarC_Class_Setlike.equal ()
                     (Obj.magic
                        (FStarC_Compiler_FlatSet.setlike_flat_set
                           FStarC_Syntax_Free.ord_univ_uvar)) (Obj.magic u1)
                     (Obj.magic u2) in
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
                                 FStarC_Class_Show.show
                                   (FStarC_Class_Show.show_either
                                      FStarC_Syntax_Print.showable_bv
                                      FStarC_Syntax_Print.showable_fv) lb1 in
                               let uu___12 =
                                 FStarC_Class_Show.show
                                   (FStarC_Class_Show.show_either
                                      FStarC_Syntax_Print.showable_bv
                                      FStarC_Syntax_Print.showable_fv) lb2 in
                               FStarC_Compiler_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu___11 uu___12 in
                             FStarC_Errors.raise_error
                               FStarC_TypeChecker_Env.hasRange_env env
                               FStarC_Errors_Codes.Fatal_IncompatibleSetOfUniverse
                               ()
                               (Obj.magic
                                  FStarC_Errors_Msg.is_error_message_string)
                               (Obj.magic msg))) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStarC_Compiler_Util.for_all
                     (fun u ->
                        FStarC_Compiler_Util.for_some
                          (fun u' ->
                             FStarC_Syntax_Unionfind.equiv
                               u.FStarC_Syntax_Syntax.ctx_uvar_head
                               u'.FStarC_Syntax_Syntax.ctx_uvar_head) u21)
                     u11 in
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
                                 FStarC_Class_Show.show
                                   (FStarC_Class_Show.show_either
                                      FStarC_Syntax_Print.showable_bv
                                      FStarC_Syntax_Print.showable_fv) lb1 in
                               let uu___12 =
                                 FStarC_Class_Show.show
                                   (FStarC_Class_Show.show_either
                                      FStarC_Syntax_Print.showable_bv
                                      FStarC_Syntax_Print.showable_fv) lb2 in
                               FStarC_Compiler_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu___11 uu___12 in
                             FStarC_Errors.raise_error
                               FStarC_TypeChecker_Env.hasRange_env env
                               FStarC_Errors_Codes.Fatal_IncompatibleNumberOfTypes
                               ()
                               (Obj.magic
                                  FStarC_Errors_Msg.is_error_message_string)
                               (Obj.magic msg))) in
               let lecs1 =
                 let uu___3 = FStarC_Compiler_List.tl lecs in
                 FStarC_Compiler_List.fold_right
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
                 FStarC_Compiler_List.concatMap
                   (fun u ->
                      if
                        FStar_Pervasives_Native.uu___is_Some
                          u.FStarC_Syntax_Syntax.ctx_uvar_meta
                      then []
                      else
                        (let uu___4 =
                           FStarC_Syntax_Unionfind.find
                             u.FStarC_Syntax_Syntax.ctx_uvar_head in
                         match uu___4 with
                         | FStar_Pervasives_Native.Some uu___5 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu___5 ->
                             let k =
                               let uu___6 = FStarC_Syntax_Util.ctx_uvar_typ u in
                               FStarC_TypeChecker_Normalize.normalize
                                 [FStarC_TypeChecker_Env.Beta;
                                 FStarC_TypeChecker_Env.Exclude
                                   FStarC_TypeChecker_Env.Zeta] env uu___6 in
                             let uu___6 = FStarC_Syntax_Util.arrow_formals k in
                             (match uu___6 with
                              | (bs, kres) ->
                                  let uu___7 =
                                    let uu___8 =
                                      let uu___9 =
                                        FStarC_TypeChecker_Normalize.unfold_whnf
                                          env kres in
                                      FStarC_Syntax_Util.unrefine uu___9 in
                                    uu___8.FStarC_Syntax_Syntax.n in
                                  (match uu___7 with
                                   | FStarC_Syntax_Syntax.Tm_type uu___8 ->
                                       let free =
                                         FStarC_Syntax_Free.names kres in
                                       let uu___9 =
                                         let uu___10 =
                                           FStarC_Class_Setlike.is_empty ()
                                             (Obj.magic
                                                (FStarC_Compiler_FlatSet.setlike_flat_set
                                                   FStarC_Syntax_Syntax.ord_bv))
                                             (Obj.magic free) in
                                         Prims.op_Negation uu___10 in
                                       if uu___9
                                       then []
                                       else
                                         (let a =
                                            let uu___11 =
                                              let uu___12 =
                                                FStarC_TypeChecker_Env.get_range
                                                  env in
                                              FStar_Pervasives_Native.Some
                                                uu___12 in
                                            FStarC_Syntax_Syntax.new_bv
                                              uu___11 kres in
                                          let t =
                                            match bs with
                                            | [] ->
                                                FStarC_Syntax_Syntax.bv_to_name
                                                  a
                                            | uu___11 ->
                                                let uu___12 =
                                                  FStarC_Syntax_Syntax.bv_to_name
                                                    a in
                                                FStarC_Syntax_Util.abs bs
                                                  uu___12
                                                  (FStar_Pervasives_Native.Some
                                                     (FStarC_Syntax_Util.residual_tot
                                                        kres)) in
                                          FStarC_Syntax_Util.set_uvar
                                            u.FStarC_Syntax_Syntax.ctx_uvar_head
                                            t;
                                          (let uu___12 =
                                             let uu___13 =
                                               FStarC_Syntax_Syntax.as_bqual_implicit
                                                 true in
                                             (a, uu___13) in
                                           [uu___12]))
                                   | uu___8 -> [])))) uvs1 in
               let gen_univs1 = gen_univs env univs in
               let gen_tvars = gen_types uvs in
               let ecs =
                 FStarC_Compiler_List.map
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
                                       FStarC_TypeChecker_Normalize.normalize_comp
                                         [FStarC_TypeChecker_Env.Beta;
                                         FStarC_TypeChecker_Env.DoNotUnfoldPureLets;
                                         FStarC_TypeChecker_Env.CompressUvars;
                                         FStarC_TypeChecker_Env.NoFullNorm;
                                         FStarC_TypeChecker_Env.Exclude
                                           FStarC_TypeChecker_Env.Zeta] env c in
                                     let e1 =
                                       FStarC_TypeChecker_Normalize.reduce_uvar_solutions
                                         env e in
                                     let e2 =
                                       if is_rec
                                       then
                                         let tvar_args =
                                           FStarC_Compiler_List.map
                                             (fun uu___7 ->
                                                match uu___7 with
                                                | (x, uu___8) ->
                                                    let uu___9 =
                                                      FStarC_Syntax_Syntax.bv_to_name
                                                        x in
                                                    FStarC_Syntax_Syntax.iarg
                                                      uu___9) gen_tvars in
                                         let instantiate_lbname_with_app tm
                                           fv =
                                           let uu___7 =
                                             let uu___8 =
                                               FStarC_Compiler_Util.right
                                                 lbname in
                                             FStarC_Syntax_Syntax.fv_eq fv
                                               uu___8 in
                                           if uu___7
                                           then
                                             FStarC_Syntax_Syntax.mk_Tm_app
                                               tm tvar_args
                                               tm.FStarC_Syntax_Syntax.pos
                                           else tm in
                                         FStarC_Syntax_InstFV.inst
                                           instantiate_lbname_with_app e1
                                       else e1 in
                                     let tvars_bs =
                                       FStarC_Compiler_List.map
                                         (fun uu___7 ->
                                            match uu___7 with
                                            | (x, q) ->
                                                FStarC_Syntax_Syntax.mk_binder_with_attrs
                                                  x q
                                                  FStar_Pervasives_Native.None
                                                  []) gen_tvars in
                                     let t =
                                       let uu___7 =
                                         let uu___8 =
                                           FStarC_Syntax_Subst.compress
                                             (FStarC_Syntax_Util.comp_result
                                                c1) in
                                         uu___8.FStarC_Syntax_Syntax.n in
                                       match uu___7 with
                                       | FStarC_Syntax_Syntax.Tm_arrow
                                           { FStarC_Syntax_Syntax.bs1 = bs;
                                             FStarC_Syntax_Syntax.comp = cod;_}
                                           ->
                                           let uu___8 =
                                             FStarC_Syntax_Subst.open_comp bs
                                               cod in
                                           (match uu___8 with
                                            | (bs1, cod1) ->
                                                FStarC_Syntax_Util.arrow
                                                  (FStarC_Compiler_List.op_At
                                                     tvars_bs bs1) cod1)
                                       | uu___8 ->
                                           FStarC_Syntax_Util.arrow tvars_bs
                                             c1 in
                                     let e' =
                                       let uu___7 =
                                         let uu___8 =
                                           FStarC_Syntax_Util.residual_comp_of_comp
                                             c1 in
                                         FStar_Pervasives_Native.Some uu___8 in
                                       FStarC_Syntax_Util.abs tvars_bs e2
                                         uu___7 in
                                     let uu___7 =
                                       FStarC_Syntax_Syntax.mk_Total t in
                                     (e', uu___7, tvars_bs)) in
                          (match uu___4 with
                           | (e1, c1, gvs) ->
                               (lbname, gen_univs1, e1, c1, gvs))) lecs2 in
               FStar_Pervasives_Native.Some ecs)
let (generalize' :
  FStarC_TypeChecker_Env.env ->
    Prims.bool ->
      (FStarC_Syntax_Syntax.lbname * FStarC_Syntax_Syntax.term *
        FStarC_Syntax_Syntax.comp) Prims.list ->
        (FStarC_Syntax_Syntax.lbname * FStarC_Syntax_Syntax.univ_names *
          FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.comp *
          FStarC_Syntax_Syntax.binder Prims.list) Prims.list)
  =
  fun env ->
    fun is_rec ->
      fun lecs ->
        (let uu___2 = FStarC_Compiler_Debug.low () in
         if uu___2
         then
           let uu___3 =
             let uu___4 =
               FStarC_Compiler_List.map
                 (fun uu___5 ->
                    match uu___5 with
                    | (lb, uu___6, uu___7) ->
                        FStarC_Class_Show.show
                          (FStarC_Class_Show.show_either
                             FStarC_Syntax_Print.showable_bv
                             FStarC_Syntax_Print.showable_fv) lb) lecs in
             FStarC_Class_Show.show
               (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
               uu___4 in
           FStarC_Compiler_Util.print1 "Generalizing: %s\n" uu___3
         else ());
        (let univnames_lecs =
           let empty =
             Obj.magic
               (FStarC_Class_Setlike.from_list ()
                  (Obj.magic
                     (FStarC_Compiler_FlatSet.setlike_flat_set
                        FStarC_Syntax_Syntax.ord_ident)) []) in
           FStarC_Compiler_List.fold_left
             (fun uu___3 ->
                fun uu___2 ->
                  (fun out ->
                     fun uu___2 ->
                       match uu___2 with
                       | (l, t, c) ->
                           let uu___3 = gather_free_univnames env t in
                           Obj.magic
                             (FStarC_Class_Setlike.union ()
                                (Obj.magic
                                   (FStarC_Compiler_FlatSet.setlike_flat_set
                                      FStarC_Syntax_Syntax.ord_ident))
                                (Obj.magic out) (Obj.magic uu___3))) uu___3
                    uu___2) empty lecs in
         let univnames_lecs1 =
           FStarC_Class_Setlike.elems ()
             (Obj.magic
                (FStarC_Compiler_FlatSet.setlike_flat_set
                   FStarC_Syntax_Syntax.ord_ident))
             (Obj.magic univnames_lecs) in
         let generalized_lecs =
           let uu___2 = gen env is_rec lecs in
           match uu___2 with
           | FStar_Pervasives_Native.None ->
               FStarC_Compiler_List.map
                 (fun uu___3 ->
                    match uu___3 with | (l, t, c) -> (l, [], t, c, [])) lecs
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu___4 = FStarC_Compiler_Debug.medium () in
                 if uu___4
                 then
                   FStarC_Compiler_List.iter
                     (fun uu___5 ->
                        match uu___5 with
                        | (l, us, e, c, gvs) ->
                            let uu___6 =
                              FStarC_Class_Show.show
                                FStarC_Compiler_Range_Ops.showable_range
                                e.FStarC_Syntax_Syntax.pos in
                            let uu___7 =
                              FStarC_Class_Show.show
                                (FStarC_Class_Show.show_either
                                   FStarC_Syntax_Print.showable_bv
                                   FStarC_Syntax_Print.showable_fv) l in
                            let uu___8 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_term
                                (FStarC_Syntax_Util.comp_result c) in
                            let uu___9 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_term e in
                            let uu___10 =
                              FStarC_Class_Show.show
                                (FStarC_Class_Show.show_list
                                   FStarC_Syntax_Print.showable_binder) gvs in
                            FStarC_Compiler_Util.print5
                              "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                              uu___6 uu___7 uu___8 uu___9 uu___10) luecs
                 else ());
                luecs) in
         FStarC_Compiler_List.map
           (fun uu___2 ->
              match uu___2 with
              | (l, generalized_univs, t, c, gvs) ->
                  let uu___3 =
                    check_universe_generalization univnames_lecs1
                      generalized_univs t in
                  (l, uu___3, t, c, gvs)) generalized_lecs)
let (generalize :
  FStarC_TypeChecker_Env.env ->
    Prims.bool ->
      (FStarC_Syntax_Syntax.lbname * FStarC_Syntax_Syntax.term *
        FStarC_Syntax_Syntax.comp) Prims.list ->
        (FStarC_Syntax_Syntax.lbname * FStarC_Syntax_Syntax.univ_names *
          FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.comp *
          FStarC_Syntax_Syntax.binder Prims.list) Prims.list)
  =
  fun env ->
    fun is_rec ->
      fun lecs ->
        FStarC_Errors.with_ctx "While generalizing"
          (fun uu___ ->
             let uu___1 =
               let uu___2 =
                 let uu___3 = FStarC_TypeChecker_Env.current_module env in
                 FStarC_Ident.string_of_lid uu___3 in
               FStar_Pervasives_Native.Some uu___2 in
             FStarC_Profiling.profile
               (fun uu___2 -> generalize' env is_rec lecs) uu___1
               "FStarC.TypeChecker.Util.generalize")