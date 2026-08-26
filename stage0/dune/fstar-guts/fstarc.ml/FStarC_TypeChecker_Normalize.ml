open Prims
let plugin_unfold_warn_ctr : Prims.int FStarC_Effect.ref=
  FStarC_Effect.mk_ref Prims.int_zero
let dbg_univ_norm : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "univ_norm"
let dbg_NormRebuild : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "NormRebuild"
let maybe_debug (cfg : FStarC_TypeChecker_Cfg.cfg)
  (t : FStarC_Syntax_Syntax.term)
  (dbg :
    (FStarC_Syntax_Syntax.term * FStarC_Timing.time_ns)
      FStar_Pervasives_Native.option)
  : unit=
  if
    (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.print_normalized
  then
    match dbg with
    | FStar_Pervasives_Native.Some (tm, time_then) ->
        let time_now = FStarC_Timing.now_ns () in
        let uu___ =
          FStarC_Class_Show.show FStarC_Class_Show.showable_int
            (FStarC_Timing.diff_ms time_then time_now) in
        let uu___1 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tm in
        let uu___2 =
          FStarC_Class_Show.show FStarC_TypeChecker_Cfg.showable_cfg cfg in
        let uu___3 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
        FStarC_Format.print4
          "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
          uu___ uu___1 uu___2 uu___3
    | uu___ -> ()
  else ()
let cases (f : 'uuuuu -> 'uuuuu1) (d : 'uuuuu1)
  (uu___ : 'uuuuu FStar_Pervasives_Native.option) : 'uuuuu1=
  match uu___ with
  | FStar_Pervasives_Native.Some x -> f x
  | FStar_Pervasives_Native.None -> d
let head_of_term_is_evaluated (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : Prims.bool=
  let uu___ = FStarC_Syntax_Util.head_and_args_full t in
  match uu___ with
  | (h, uu___1) ->
      let h1 =
        let uu___2 =
          let uu___3 = FStarC_Syntax_Util.unlazy h in
          FStarC_Syntax_Util.unmeta uu___3 in
        FStarC_Syntax_Util.un_uinst uu___2 in
      let uu___2 =
        let uu___3 = FStarC_Syntax_Subst.compress h1 in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_constant uu___3 -> true
       | FStarC_Syntax_Syntax.Tm_fvar fv ->
           FStarC_TypeChecker_Env.is_datacon env
             fv.FStarC_Syntax_Syntax.fv_name
       | uu___3 -> false)
let guard (b : Prims.bool) : unit FStar_Pervasives_Native.option=
  if b then FStar_Pervasives_Native.Some () else FStar_Pervasives_Native.None
let check_strict_app (cfg : FStarC_TypeChecker_Cfg.cfg)
  (hua :
    (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.universes *
      FStarC_Syntax_Syntax.args))
  : Prims.bool=
  let uu___ = hua in
  match uu___ with
  | (h, u, a) ->
      let uu___1 =
        FStarC_TypeChecker_Env.fv_has_strict_args
          cfg.FStarC_TypeChecker_Cfg.tcenv h in
      (match uu___1 with
       | FStar_Pervasives_Native.None -> false
       | FStar_Pervasives_Native.Some strict_indices ->
           (FStarC_TypeChecker_Cfg.log cfg
              (fun uu___3 ->
                 let uu___4 =
                   FStarC_Class_Show.show
                     (FStarC_Class_Show.show_tuple3
                        FStarC_Syntax_Syntax.showable_fv
                        (FStarC_Class_Show.show_list
                           FStarC_Syntax_Print.showable_univ)
                        (FStarC_Class_Show.show_list
                           (FStarC_Class_Show.show_tuple2
                              FStarC_Syntax_Print.showable_term
                              FStarC_Syntax_Print.showable_aqual))) hua in
                 let uu___5 =
                   FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_fv h in
                 let uu___6 =
                   FStarC_Class_Show.show
                     (FStarC_Class_Show.show_list
                        FStarC_Class_Show.showable_int) strict_indices in
                 FStarC_Format.print3
                   "Checking strict application for %s, head=%s, strict_indices=%s\n"
                   uu___4 uu___5 uu___6);
            (let len_a = FStarC_List.length a in
             let all_ok =
               FStarC_List.for_all
                 (fun i ->
                    if i >= len_a
                    then false
                    else
                      head_of_term_is_evaluated
                        cfg.FStarC_TypeChecker_Cfg.tcenv
                        (FStar_Pervasives_Native.fst (FStarC_List.nth a i)))
                 strict_indices in
             all_ok)))
let check_strict_projector (cfg : FStarC_TypeChecker_Cfg.cfg)
  (hua :
    (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.universes *
      FStarC_Syntax_Syntax.args))
  : Prims.bool=
  let uu___ = hua in
  match uu___ with
  | (h, u, a) ->
      let uu___1 =
        let uu___2 =
          FStarC_TypeChecker_Env.is_projector
            cfg.FStarC_TypeChecker_Cfg.tcenv h.FStarC_Syntax_Syntax.fv_name in
        Prims.not uu___2 in
      if uu___1
      then false
      else
        (let rec check args =
           match args with
           | [] -> false
           | (last, last_q)::[] ->
               if
                 (match last_q with
                  | FStar_Pervasives_Native.None -> true
                  | uu___2 -> false)
               then
                 head_of_term_is_evaluated cfg.FStarC_TypeChecker_Cfg.tcenv
                   last
               else false
           | a1::args' ->
               if
                 (match FStar_Pervasives_Native.snd a1 with
                  | FStar_Pervasives_Native.Some v -> true
                  | uu___2 -> false)
               then check args'
               else false in
         check a)
let disc_proj_head (cfg : FStarC_TypeChecker_Cfg.cfg)
  (head : FStarC_Syntax_Syntax.term) :
  (FStarC_Ident.lident * Prims.bool * Prims.int * Prims.int
    FStar_Pervasives_Native.option) FStar_Pervasives_Native.option=
  if Prims.not (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.iota
  then FStar_Pervasives_Native.None
  else
    (let uu___ =
       let uu___1 = FStarC_Syntax_Util.un_uinst head in
       uu___1.FStarC_Syntax_Syntax.n in
     match uu___ with
     | FStarC_Syntax_Syntax.Tm_fvar h ->
         let uu___1 =
           FStarC_TypeChecker_Env.disc_proj_info
             cfg.FStarC_TypeChecker_Cfg.tcenv h.FStarC_Syntax_Syntax.fv_name in
         (match uu___1 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (q, n_indexed, idx) ->
              (match q with
               | FStarC_Syntax_Syntax.Projector (d, uu___2) ->
                   FStar_Pervasives_Native.Some (d, false, n_indexed, idx)
               | FStarC_Syntax_Syntax.Discriminator d ->
                   FStar_Pervasives_Native.Some (d, true, n_indexed, idx)
               | uu___2 ->
                   FStarC_Effect.failwith "disc_proj_head: impossible"))
     | uu___1 -> FStar_Pervasives_Native.None)
let reduce_disc_proj (cfg : FStarC_TypeChecker_Cfg.cfg)
  (d : FStarC_Ident.lident) (is_disc : Prims.bool)
  (idx : Prims.int FStar_Pervasives_Native.option)
  (scrutinee : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Syntax_Util.unmeta scrutinee in
      FStarC_Syntax_Util.unlazy uu___2 in
    FStarC_Syntax_Util.hua uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (c, uu___1, cargs) ->
      let uu___2 =
        let uu___3 =
          FStarC_TypeChecker_Env.is_datacon cfg.FStarC_TypeChecker_Cfg.tcenv
            c.FStarC_Syntax_Syntax.fv_name in
        Prims.not uu___3 in
      if uu___2
      then FStar_Pervasives_Native.None
      else
        (let same = FStarC_Ident.lid_equals c.FStarC_Syntax_Syntax.fv_name d in
         if is_disc
         then
           FStar_Pervasives_Native.Some
             ((if same
               then FStarC_Syntax_Util.exp_true_bool
               else FStarC_Syntax_Util.exp_false_bool))
         else
           if Prims.not same
           then FStar_Pervasives_Native.None
           else
             (match idx with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  if (FStarC_List.length cargs) <= i
                  then FStar_Pervasives_Native.None
                  else
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.fst (FStarC_List.nth cargs i))))
let disc_proj_lb (tcenv : FStarC_TypeChecker_Env.env)
  (lid : FStarC_Ident.lident) (us : FStarC_Syntax_Syntax.univ_names)
  (t : FStarC_Syntax_Syntax.typ) (q : FStarC_Syntax_Syntax.qualifier) :
  FStarC_Syntax_Syntax.letbinding FStar_Pervasives_Native.option=
  let d =
    match q with
    | FStarC_Syntax_Syntax.Projector (d1, uu___) -> d1
    | FStarC_Syntax_Syntax.Discriminator d1 -> d1
    | uu___ -> FStarC_Effect.failwith "disc_proj_lb: impossible" in
  let uu___ = FStarC_TypeChecker_Env.datacon_decl tcenv d in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (fvq, ntps, (dus, dt)) ->
      let uu___1 = FStarC_Syntax_Subst.open_univ_vars us t in
      (match uu___1 with
       | (us1, t') ->
           let uu___2 = FStarC_Syntax_Util.arrow_formals t' in
           (match uu___2 with
            | (binders, uu___3) ->
                let dt1 =
                  if (FStarC_List.length dus) = (FStarC_List.length us1)
                  then
                    let uu___4 =
                      let uu___5 =
                        FStarC_List.map
                          (fun uu___6 -> FStarC_Syntax_Syntax.U_name uu___6)
                          us1 in
                      FStarC_TypeChecker_Env.inst_tscheme_with (dus, dt)
                        uu___5 in
                    FStar_Pervasives_Native.snd uu___4
                  else
                    (let uu___4 = FStarC_Syntax_Subst.open_univ_vars dus dt in
                     FStar_Pervasives_Native.snd uu___4) in
                let uu___4 = FStarC_Syntax_Util.arrow_formals dt1 in
                (match uu___4 with
                 | (cbs, dres) ->
                     let n_imp =
                       let uu___5 =
                         let uu___6 =
                           FStarC_Syntax_Util.head_and_args_full dres in
                         FStar_Pervasives_Native.snd uu___6 in
                       FStarC_List.length uu___5 in
                     if
                       (((FStarC_List.length binders) <= n_imp) ||
                          ((FStarC_List.length cbs) < ntps))
                         || (n_imp < ntps)
                     then FStar_Pervasives_Native.None
                     else
                       (let uu___5 =
                          FStarC_Util.first_N (n_imp + Prims.int_one) binders in
                        match uu___5 with
                        | (binders1, uu___6) ->
                            let arg_exp =
                              FStarC_Syntax_Syntax.bv_to_name
                                (FStarC_List.last binders1).FStarC_Syntax_Syntax.binder_bv in
                            let uu___7 = FStarC_Util.first_N ntps cbs in
                            (match uu___7 with
                             | (cparams, cfields) ->
                                 let uu___8 =
                                   FStarC_Util.first_N ntps binders1 in
                                 (match uu___8 with
                                  | (ty_params, uu___9) ->
                                      let subst =
                                        FStarC_List.map2
                                          (fun cb b ->
                                             let uu___10 =
                                               let uu___11 =
                                                 FStarC_Syntax_Syntax.bv_to_name
                                                   b.FStarC_Syntax_Syntax.binder_bv in
                                               ((cb.FStarC_Syntax_Syntax.binder_bv),
                                                 uu___11) in
                                             FStarC_Syntax_Syntax.NT uu___10)
                                          cparams ty_params in
                                      let uu___10 =
                                        FStarC_List.fold_left
                                          (fun uu___11 cb ->
                                             match uu___11 with
                                             | (subst1, out) ->
                                                 let x =
                                                   let uu___12 =
                                                     FStarC_Syntax_Subst.subst
                                                       subst1
                                                       (cb.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                   FStarC_Syntax_Syntax.gen_bv
                                                     (FStarC_Ident.string_of_id
                                                        (cb.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname)
                                                     FStar_Pervasives_Native.None
                                                     uu___12 in
                                                 let uu___12 =
                                                   let uu___13 =
                                                     let uu___14 =
                                                       let uu___15 =
                                                         FStarC_Syntax_Syntax.bv_to_name
                                                           x in
                                                       ((cb.FStarC_Syntax_Syntax.binder_bv),
                                                         uu___15) in
                                                     FStarC_Syntax_Syntax.NT
                                                       uu___14 in
                                                   uu___13 :: subst1 in
                                                 (uu___12, (x :: out)))
                                          (subst, []) cfields in
                                      (match uu___10 with
                                       | (uu___11, field_bvs) ->
                                           let field_bvs1 =
                                             FStarC_List.rev field_bvs in
                                           let arg_pats =
                                             let uu___12 =
                                               FStarC_List.map
                                                 (fun b ->
                                                    let uu___13 =
                                                      let uu___14 =
                                                        let uu___15 =
                                                          let uu___16 =
                                                            FStarC_Syntax_Syntax.bv_to_name
                                                              b.FStarC_Syntax_Syntax.binder_bv in
                                                          FStar_Pervasives_Native.Some
                                                            uu___16 in
                                                        FStarC_Syntax_Syntax.Pat_dot_term
                                                          uu___15 in
                                                      FStarC_Syntax_Syntax.withinfo
                                                        uu___14
                                                        FStarC_Range_Type.dummyRange in
                                                    (uu___13, true))
                                                 ty_params in
                                             let uu___13 =
                                               FStarC_List.map2
                                                 (fun cb x ->
                                                    ((FStarC_Syntax_Syntax.withinfo
                                                        (FStarC_Syntax_Syntax.Pat_var
                                                           x)
                                                        FStarC_Range_Type.dummyRange),
                                                      (FStarC_Syntax_Syntax.is_bqual_implicit_or_meta
                                                         cb.FStarC_Syntax_Syntax.binder_qual)))
                                                 cfields field_bvs1 in
                                             FStarC_List.op_At uu___12
                                               uu___13 in
                                           let pat_cons =
                                             FStarC_Syntax_Syntax.withinfo
                                               (FStarC_Syntax_Syntax.Pat_cons
                                                  ((FStarC_Syntax_Syntax.lid_as_fv
                                                      d
                                                      (FStar_Pervasives_Native.Some
                                                         fvq)),
                                                    FStar_Pervasives_Native.None,
                                                    arg_pats))
                                               FStarC_Range_Type.dummyRange in
                                           let body_opt =
                                             match q with
                                             | FStarC_Syntax_Syntax.Discriminator
                                                 uu___12 ->
                                                 let uu___13 =
                                                   let uu___14 =
                                                     let uu___15 =
                                                       let uu___16 =
                                                         let uu___17 =
                                                           FStarC_TypeChecker_Env.typ_of_datacon
                                                             tcenv d in
                                                         FStarC_TypeChecker_Env.datacons_of_typ
                                                           tcenv uu___17 in
                                                       FStar_Pervasives_Native.snd
                                                         uu___16 in
                                                     FStarC_List.length
                                                       uu___15 in
                                                   uu___14 <= Prims.int_one in
                                                 if uu___13
                                                 then
                                                   FStar_Pervasives_Native.Some
                                                     FStarC_Syntax_Util.exp_true_bool
                                                 else
                                                   (let wild =
                                                      FStarC_Syntax_Syntax.new_bv
                                                        FStar_Pervasives_Native.None
                                                        ((FStarC_List.last
                                                            binders1).FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                    let uu___14 =
                                                      let uu___15 =
                                                        let uu___16 =
                                                          let uu___17 =
                                                            let uu___18 =
                                                              FStarC_Syntax_Util.branch
                                                                (pat_cons,
                                                                  FStar_Pervasives_Native.None,
                                                                  FStarC_Syntax_Util.exp_true_bool) in
                                                            let uu___19 =
                                                              let uu___20 =
                                                                FStarC_Syntax_Util.branch
                                                                  ((FStarC_Syntax_Syntax.withinfo
                                                                    (FStarC_Syntax_Syntax.Pat_var
                                                                    wild)
                                                                    FStarC_Range_Type.dummyRange),
                                                                    FStar_Pervasives_Native.None,
                                                                    FStarC_Syntax_Util.exp_false_bool) in
                                                              [uu___20] in
                                                            uu___18 ::
                                                              uu___19 in
                                                          {
                                                            FStarC_Syntax_Syntax.scrutinee
                                                              = arg_exp;
                                                            FStarC_Syntax_Syntax.ret_opt
                                                              =
                                                              FStar_Pervasives_Native.None;
                                                            FStarC_Syntax_Syntax.brs
                                                              = uu___17;
                                                            FStarC_Syntax_Syntax.rc_opt1
                                                              =
                                                              FStar_Pervasives_Native.None
                                                          } in
                                                        FStarC_Syntax_Syntax.Tm_match
                                                          uu___16 in
                                                      FStarC_Syntax_Syntax.mk
                                                        uu___15
                                                        FStarC_Range_Type.dummyRange in
                                                    FStar_Pervasives_Native.Some
                                                      uu___14)
                                             | uu___12 ->
                                                 let idx =
                                                   let uu___13 =
                                                     FStarC_List.mapi
                                                       (fun j b -> (j, b))
                                                       cfields in
                                                   FStarC_List.tryPick
                                                     (fun uu___14 ->
                                                        match uu___14 with
                                                        | (j,
                                                           {
                                                             FStarC_Syntax_Syntax.binder_bv
                                                               = x;
                                                             FStarC_Syntax_Syntax.binder_qual
                                                               = uu___15;
                                                             FStarC_Syntax_Syntax.binder_positivity
                                                               = uu___16;
                                                             FStarC_Syntax_Syntax.binder_attrs
                                                               = uu___17;_})
                                                            ->
                                                            let uu___18 =
                                                              let uu___19 =
                                                                FStarC_Syntax_Util.mk_field_projector_name
                                                                  d x j in
                                                              FStarC_Ident.lid_equals
                                                                uu___19 lid in
                                                            if uu___18
                                                            then
                                                              FStar_Pervasives_Native.Some
                                                                j
                                                            else
                                                              FStar_Pervasives_Native.None)
                                                     uu___13 in
                                                 (match idx with
                                                  | FStar_Pervasives_Native.None
                                                      ->
                                                      FStar_Pervasives_Native.None
                                                  | FStar_Pervasives_Native.Some
                                                      i ->
                                                      let uu___13 =
                                                        let uu___14 =
                                                          let uu___15 =
                                                            let uu___16 =
                                                              let uu___17 =
                                                                let uu___18 =
                                                                  let uu___19
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    (FStarC_List.nth
                                                                    field_bvs1
                                                                    i) in
                                                                  (pat_cons,
                                                                    FStar_Pervasives_Native.None,
                                                                    uu___19) in
                                                                FStarC_Syntax_Util.branch
                                                                  uu___18 in
                                                              [uu___17] in
                                                            {
                                                              FStarC_Syntax_Syntax.scrutinee
                                                                = arg_exp;
                                                              FStarC_Syntax_Syntax.ret_opt
                                                                =
                                                                FStar_Pervasives_Native.None;
                                                              FStarC_Syntax_Syntax.brs
                                                                = uu___16;
                                                              FStarC_Syntax_Syntax.rc_opt1
                                                                =
                                                                FStar_Pervasives_Native.None
                                                            } in
                                                          FStarC_Syntax_Syntax.Tm_match
                                                            uu___15 in
                                                        FStarC_Syntax_Syntax.mk
                                                          uu___14
                                                          FStarC_Range_Type.dummyRange in
                                                      FStar_Pervasives_Native.Some
                                                        uu___13) in
                                           (match body_opt with
                                            | FStar_Pervasives_Native.None ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some
                                                body ->
                                                let imp =
                                                  FStarC_Syntax_Util.abs
                                                    binders1 body
                                                    FStar_Pervasives_Native.None in
                                                let uu___12 =
                                                  let uu___13 =
                                                    FStarC_Syntax_Subst.close_univ_vars
                                                      us1 imp in
                                                  FStarC_Syntax_Util.mk_letbinding
                                                    (FStar_Pervasives.Inr
                                                       (FStarC_Syntax_Syntax.lid_and_dd_as_fv
                                                          lid
                                                          FStar_Pervasives_Native.None))
                                                    us1 t
                                                    FStarC_Parser_Const.effect_Tot_lid
                                                    uu___13 []
                                                    FStarC_Range_Type.dummyRange in
                                                FStar_Pervasives_Native.Some
                                                  uu___12))))))))
let unfold_disc_proj_for_extraction (cfg : FStarC_TypeChecker_Cfg.cfg)
  (head : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option=
  if
    Prims.not
      (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
  then FStar_Pervasives_Native.None
  else
    (let uu___ =
       let uu___1 = FStarC_Syntax_Subst.compress head in
       uu___1.FStarC_Syntax_Syntax.n in
     match uu___ with
     | FStarC_Syntax_Syntax.Tm_fvar fv ->
         if
           (match FStarC_Option.dflt FStarC_Syntax_Syntax.Data_ctor
                    fv.FStarC_Syntax_Syntax.fv_qual
            with
            | FStarC_Syntax_Syntax.Record_projector _0 -> true
            | uu___1 -> false)
         then FStar_Pervasives_Native.None
         else
           (let lid = fv.FStarC_Syntax_Syntax.fv_name in
            let uu___1 =
              FStarC_TypeChecker_Env.disc_proj_qual
                cfg.FStarC_TypeChecker_Cfg.tcenv lid in
            match uu___1 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some q ->
                let uu___2 =
                  FStarC_TypeChecker_Env.lookup_qname
                    cfg.FStarC_TypeChecker_Cfg.tcenv lid in
                (match uu___2 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Pervasives.Inr
                      ({
                         FStarC_Syntax_Syntax.sigel =
                           FStarC_Syntax_Syntax.Sig_declare_typ
                           { FStarC_Syntax_Syntax.lid2 = uu___3;
                             FStarC_Syntax_Syntax.us2 = dus;
                             FStarC_Syntax_Syntax.t2 = t;_};
                         FStarC_Syntax_Syntax.sigrng = uu___4;
                         FStarC_Syntax_Syntax.sigquals = uu___5;
                         FStarC_Syntax_Syntax.sigmeta = uu___6;
                         FStarC_Syntax_Syntax.sigattrs = uu___7;
                         FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___8;
                         FStarC_Syntax_Syntax.sigopts = uu___9;_},
                       uu___10),
                      uu___11)
                     ->
                     let uu___12 =
                       disc_proj_lb cfg.FStarC_TypeChecker_Cfg.tcenv lid dus
                         t q in
                     (match uu___12 with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some lb ->
                          FStar_Pervasives_Native.Some
                            ((lb.FStarC_Syntax_Syntax.lbunivs),
                              (lb.FStarC_Syntax_Syntax.lbdef)))
                 | uu___3 -> FStar_Pervasives_Native.None))
     | FStarC_Syntax_Syntax.Tm_uinst
         ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
            FStarC_Syntax_Syntax.pos = uu___1;
            FStarC_Syntax_Syntax.hash_code = uu___2;_},
          uu___3)
         ->
         if
           (match FStarC_Option.dflt FStarC_Syntax_Syntax.Data_ctor
                    fv.FStarC_Syntax_Syntax.fv_qual
            with
            | FStarC_Syntax_Syntax.Record_projector _0 -> true
            | uu___4 -> false)
         then FStar_Pervasives_Native.None
         else
           (let lid = fv.FStarC_Syntax_Syntax.fv_name in
            let uu___4 =
              FStarC_TypeChecker_Env.disc_proj_qual
                cfg.FStarC_TypeChecker_Cfg.tcenv lid in
            match uu___4 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some q ->
                let uu___5 =
                  FStarC_TypeChecker_Env.lookup_qname
                    cfg.FStarC_TypeChecker_Cfg.tcenv lid in
                (match uu___5 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Pervasives.Inr
                      ({
                         FStarC_Syntax_Syntax.sigel =
                           FStarC_Syntax_Syntax.Sig_declare_typ
                           { FStarC_Syntax_Syntax.lid2 = uu___6;
                             FStarC_Syntax_Syntax.us2 = dus;
                             FStarC_Syntax_Syntax.t2 = t;_};
                         FStarC_Syntax_Syntax.sigrng = uu___7;
                         FStarC_Syntax_Syntax.sigquals = uu___8;
                         FStarC_Syntax_Syntax.sigmeta = uu___9;
                         FStarC_Syntax_Syntax.sigattrs = uu___10;
                         FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___11;
                         FStarC_Syntax_Syntax.sigopts = uu___12;_},
                       uu___13),
                      uu___14)
                     ->
                     let uu___15 =
                       disc_proj_lb cfg.FStarC_TypeChecker_Cfg.tcenv lid dus
                         t q in
                     (match uu___15 with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some lb ->
                          FStar_Pervasives_Native.Some
                            ((lb.FStarC_Syntax_Syntax.lbunivs),
                              (lb.FStarC_Syntax_Syntax.lbdef)))
                 | uu___6 -> FStar_Pervasives_Native.None))
     | uu___1 -> FStar_Pervasives_Native.None)
let check_strict (cfg : FStarC_TypeChecker_Cfg.cfg)
  (hua :
    (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.universes *
      FStarC_Syntax_Syntax.args))
  : Prims.bool FStar_Pervasives_Native.option=
  let uu___ = check_strict_app cfg hua in
  if uu___
  then
    (FStarC_TypeChecker_Cfg.log cfg
       (fun uu___2 ->
          let uu___3 =
            FStarC_Class_Show.show
              (FStarC_Class_Show.show_tuple3 FStarC_Syntax_Syntax.showable_fv
                 (FStarC_Class_Show.show_list
                    FStarC_Syntax_Print.showable_univ)
                 (FStarC_Class_Show.show_list
                    (FStarC_Class_Show.show_tuple2
                       FStarC_Syntax_Print.showable_term
                       FStarC_Syntax_Print.showable_aqual))) hua in
          FStarC_Format.print1 "Strict application detected for %s\n" uu___3);
     FStar_Pervasives_Native.Some false)
  else
    (let uu___1 =
       if
         (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.reduce_projections
           && (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.iota
       then check_strict_projector cfg hua
       else false in
     if uu___1
     then
       (FStarC_TypeChecker_Cfg.log cfg
          (fun uu___3 ->
             let uu___4 =
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_tuple3
                    FStarC_Syntax_Syntax.showable_fv
                    (FStarC_Class_Show.show_list
                       FStarC_Syntax_Print.showable_univ)
                    (FStarC_Class_Show.show_list
                       (FStarC_Class_Show.show_tuple2
                          FStarC_Syntax_Print.showable_term
                          FStarC_Syntax_Print.showable_aqual))) hua in
             FStarC_Format.print1 "Strict projector detected for %s\n" uu___4);
        FStar_Pervasives_Native.Some true)
     else FStar_Pervasives_Native.None)
type 'a cfg_memo =
  {
  weak_memo: (FStarC_TypeChecker_Cfg.cfg * 'a) FStarC_Syntax_Syntax.memo ;
  whnf_memo: (FStarC_TypeChecker_Cfg.cfg * 'a) FStarC_Syntax_Syntax.memo ;
  strong_memo: (FStarC_TypeChecker_Cfg.cfg * 'a) FStarC_Syntax_Syntax.memo }
let __proj__Mkcfg_memo__item__weak_memo (projectee : 'a cfg_memo) :
  (FStarC_TypeChecker_Cfg.cfg * 'a) FStarC_Syntax_Syntax.memo=
  match projectee with | { weak_memo; whnf_memo; strong_memo;_} -> weak_memo
let __proj__Mkcfg_memo__item__whnf_memo (projectee : 'a cfg_memo) :
  (FStarC_TypeChecker_Cfg.cfg * 'a) FStarC_Syntax_Syntax.memo=
  match projectee with | { weak_memo; whnf_memo; strong_memo;_} -> whnf_memo
let __proj__Mkcfg_memo__item__strong_memo (projectee : 'a cfg_memo) :
  (FStarC_TypeChecker_Cfg.cfg * 'a) FStarC_Syntax_Syntax.memo=
  match projectee with
  | { weak_memo; whnf_memo; strong_memo;_} -> strong_memo
let fresh_memo (uu___ : unit) : 'a FStarC_Syntax_Syntax.memo=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let fresh_cfg_memo (uu___ : unit) : 'a cfg_memo=
  let uu___1 = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  let uu___2 = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  let uu___3 = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  { weak_memo = uu___1; whnf_memo = uu___2; strong_memo = uu___3 }
let memo_cell (cfg : FStarC_TypeChecker_Cfg.cfg) (r : 'a cfg_memo) :
  (FStarC_TypeChecker_Cfg.cfg * 'a) FStarC_Syntax_Syntax.memo=
  if Prims.not (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
  then r.strong_memo
  else
    if (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.hnf
    then r.whnf_memo
    else r.weak_memo
let other_memo_cells (cfg : FStarC_TypeChecker_Cfg.cfg) (r : 'a cfg_memo) :
  (FStarC_TypeChecker_Cfg.cfg * 'a) FStarC_Syntax_Syntax.memo Prims.list=
  if Prims.not (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
  then [r.weak_memo; r.whnf_memo]
  else
    if (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.hnf
    then [r.weak_memo; r.strong_memo]
    else [r.whnf_memo; r.strong_memo]
type closure =
  | Clos of ((FStarC_Syntax_Syntax.binder FStar_Pervasives_Native.option *
  closure * FStarC_Syntax_Syntax.subst_t FStarC_Syntax_Syntax.memo)
  Prims.list * FStarC_Syntax_Syntax.term * ((FStarC_Syntax_Syntax.binder
  FStar_Pervasives_Native.option * closure * FStarC_Syntax_Syntax.subst_t
  FStarC_Syntax_Syntax.memo) Prims.list * FStarC_Syntax_Syntax.term) cfg_memo
  * Prims.bool) 
  | Univ of FStarC_Syntax_Syntax.universe 
  | Dummy 
let uu___is_Clos (projectee : closure) : Prims.bool=
  match projectee with | Clos _0 -> true | uu___ -> false
let __proj__Clos__item___0 (projectee : closure) :
  ((FStarC_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure *
    FStarC_Syntax_Syntax.subst_t FStarC_Syntax_Syntax.memo) Prims.list *
    FStarC_Syntax_Syntax.term * ((FStarC_Syntax_Syntax.binder
    FStar_Pervasives_Native.option * closure * FStarC_Syntax_Syntax.subst_t
    FStarC_Syntax_Syntax.memo) Prims.list * FStarC_Syntax_Syntax.term)
    cfg_memo * Prims.bool)=
  match projectee with | Clos _0 -> _0
let uu___is_Univ (projectee : closure) : Prims.bool=
  match projectee with | Univ _0 -> true | uu___ -> false
let __proj__Univ__item___0 (projectee : closure) :
  FStarC_Syntax_Syntax.universe= match projectee with | Univ _0 -> _0
let uu___is_Dummy (projectee : closure) : Prims.bool=
  match projectee with | Dummy -> true | uu___ -> false
type env =
  (FStarC_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure *
    FStarC_Syntax_Syntax.subst_t FStarC_Syntax_Syntax.memo) Prims.list
let showable_memo (uu___ : 'a FStarC_Class_Show.showable) :
  'a FStarC_Syntax_Syntax.memo FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun m ->
         let uu___1 = FStarC_Effect.op_Bang m in
         match uu___1 with
         | FStar_Pervasives_Native.None -> "no_memo"
         | FStar_Pervasives_Native.Some x ->
             let uu___2 = FStarC_Class_Show.show uu___ x in
             Prims.strcat "memo=" uu___2)
  }
let empty_env : env= []
let dummy (uu___ : unit) :
  (FStarC_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure *
    FStarC_Syntax_Syntax.subst_t FStarC_Syntax_Syntax.memo)=
  let uu___1 = fresh_memo () in (FStar_Pervasives_Native.None, Dummy, uu___1)
type branches =
  (FStarC_Syntax_Syntax.pat * FStarC_Syntax_Syntax.term
    FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term) Prims.list
type stack_elt =
  | Arg of (closure * FStarC_Syntax_Syntax.aqual * FStarC_Range_Type.t) 
  | UnivArgs of (FStarC_Syntax_Syntax.universe Prims.list *
  FStarC_Range_Type.t) 
  | MemoLazy of (env * FStarC_Syntax_Syntax.term) cfg_memo 
  | Match of (env * FStarC_Syntax_Syntax.match_returns_ascription
  FStar_Pervasives_Native.option * branches *
  FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
  FStarC_TypeChecker_Cfg.cfg * FStarC_Range_Type.t) 
  | Abs of (env * FStarC_Syntax_Syntax.binders * env *
  FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
  FStarC_Range_Type.t) 
  | App of (env * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.aqual *
  FStarC_Range_Type.t) 
  | CBVApp of (env * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.aqual *
  FStarC_Range_Type.t) 
  | Meta of (env * FStarC_Syntax_Syntax.metadata * FStarC_Range_Type.t) 
  | Let of (env * FStarC_Syntax_Syntax.binders *
  FStarC_Syntax_Syntax.letbinding * FStarC_Range_Type.t) 
let uu___is_Arg (projectee : stack_elt) : Prims.bool=
  match projectee with | Arg _0 -> true | uu___ -> false
let __proj__Arg__item___0 (projectee : stack_elt) :
  (closure * FStarC_Syntax_Syntax.aqual * FStarC_Range_Type.t)=
  match projectee with | Arg _0 -> _0
let uu___is_UnivArgs (projectee : stack_elt) : Prims.bool=
  match projectee with | UnivArgs _0 -> true | uu___ -> false
let __proj__UnivArgs__item___0 (projectee : stack_elt) :
  (FStarC_Syntax_Syntax.universe Prims.list * FStarC_Range_Type.t)=
  match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy (projectee : stack_elt) : Prims.bool=
  match projectee with | MemoLazy _0 -> true | uu___ -> false
let __proj__MemoLazy__item___0 (projectee : stack_elt) :
  (env * FStarC_Syntax_Syntax.term) cfg_memo=
  match projectee with | MemoLazy _0 -> _0
let uu___is_Match (projectee : stack_elt) : Prims.bool=
  match projectee with | Match _0 -> true | uu___ -> false
let __proj__Match__item___0 (projectee : stack_elt) :
  (env * FStarC_Syntax_Syntax.match_returns_ascription
    FStar_Pervasives_Native.option * branches *
    FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
    FStarC_TypeChecker_Cfg.cfg * FStarC_Range_Type.t)=
  match projectee with | Match _0 -> _0
let uu___is_Abs (projectee : stack_elt) : Prims.bool=
  match projectee with | Abs _0 -> true | uu___ -> false
let __proj__Abs__item___0 (projectee : stack_elt) :
  (env * FStarC_Syntax_Syntax.binders * env *
    FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
    FStarC_Range_Type.t)=
  match projectee with | Abs _0 -> _0
let uu___is_App (projectee : stack_elt) : Prims.bool=
  match projectee with | App _0 -> true | uu___ -> false
let __proj__App__item___0 (projectee : stack_elt) :
  (env * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.aqual *
    FStarC_Range_Type.t)=
  match projectee with | App _0 -> _0
let uu___is_CBVApp (projectee : stack_elt) : Prims.bool=
  match projectee with | CBVApp _0 -> true | uu___ -> false
let __proj__CBVApp__item___0 (projectee : stack_elt) :
  (env * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.aqual *
    FStarC_Range_Type.t)=
  match projectee with | CBVApp _0 -> _0
let uu___is_Meta (projectee : stack_elt) : Prims.bool=
  match projectee with | Meta _0 -> true | uu___ -> false
let __proj__Meta__item___0 (projectee : stack_elt) :
  (env * FStarC_Syntax_Syntax.metadata * FStarC_Range_Type.t)=
  match projectee with | Meta _0 -> _0
let uu___is_Let (projectee : stack_elt) : Prims.bool=
  match projectee with | Let _0 -> true | uu___ -> false
let __proj__Let__item___0 (projectee : stack_elt) :
  (env * FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.letbinding *
    FStarC_Range_Type.t)=
  match projectee with | Let _0 -> _0
type stack = stack_elt Prims.list
let head_of (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let uu___ = FStarC_Syntax_Util.head_and_args_full t in
  match uu___ with | (hd, uu___1) -> hd
let cfg_equivalent (c1 : FStarC_TypeChecker_Cfg.cfg)
  (c2 : FStarC_TypeChecker_Cfg.cfg) : Prims.bool=
  let uu___ =
    let uu___1 =
      if
        (c1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak =
          (c2.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
      then
        FStarC_Class_Deq.op_Equals_Question FStarC_TypeChecker_Cfg.deq_fsteps
          c1.FStarC_TypeChecker_Cfg.steps c2.FStarC_TypeChecker_Cfg.steps
      else false in
    if uu___1
    then
      FStarC_Class_Deq.op_Equals_Question
        (FStarC_Class_Deq.deq_list FStarC_TypeChecker_Env.deq_delta_level)
        c1.FStarC_TypeChecker_Cfg.delta_level
        c2.FStarC_TypeChecker_Cfg.delta_level
    else false in
  if uu___
  then
    FStarC_Class_Deq.op_Equals_Question
      (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
      c1.FStarC_TypeChecker_Cfg.normalize_pure_lets
      c2.FStarC_TypeChecker_Cfg.normalize_pure_lets
  else false
let weak_cfg_cache :
  (FStarC_TypeChecker_Cfg.cfg * FStarC_TypeChecker_Cfg.cfg)
    FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let weak_cfg (cfg : FStarC_TypeChecker_Cfg.cfg) : FStarC_TypeChecker_Cfg.cfg=
  if (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
  then cfg
  else
    (let uu___ = FStarC_Effect.op_Bang weak_cfg_cache in
     match uu___ with
     | FStar_Pervasives_Native.Some (cfg0, cfg0') when
         FStarC_Util.physical_equality cfg cfg0 -> cfg0'
     | uu___1 ->
         let cfg' =
           {
             FStarC_TypeChecker_Cfg.steps =
               (let uu___2 = cfg.FStarC_TypeChecker_Cfg.steps in
                {
                  FStarC_TypeChecker_Cfg.beta =
                    (uu___2.FStarC_TypeChecker_Cfg.beta);
                  FStarC_TypeChecker_Cfg.iota =
                    (uu___2.FStarC_TypeChecker_Cfg.iota);
                  FStarC_TypeChecker_Cfg.zeta =
                    (uu___2.FStarC_TypeChecker_Cfg.zeta);
                  FStarC_TypeChecker_Cfg.zeta_full =
                    (uu___2.FStarC_TypeChecker_Cfg.zeta_full);
                  FStarC_TypeChecker_Cfg.weak = true;
                  FStarC_TypeChecker_Cfg.hnf =
                    (uu___2.FStarC_TypeChecker_Cfg.hnf);
                  FStarC_TypeChecker_Cfg.primops =
                    (uu___2.FStarC_TypeChecker_Cfg.primops);
                  FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___2.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStarC_TypeChecker_Cfg.unfold_until =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_until);
                  FStarC_TypeChecker_Cfg.unfold_only =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_only);
                  FStarC_TypeChecker_Cfg.unfold_once =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_once);
                  FStarC_TypeChecker_Cfg.unfold_fully =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_fully);
                  FStarC_TypeChecker_Cfg.unfold_attr =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_attr);
                  FStarC_TypeChecker_Cfg.unfold_qual =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_qual);
                  FStarC_TypeChecker_Cfg.unfold_namespace =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_namespace);
                  FStarC_TypeChecker_Cfg.dont_unfold_attr =
                    (uu___2.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                  FStarC_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___2.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStarC_TypeChecker_Cfg.simplify =
                    (uu___2.FStarC_TypeChecker_Cfg.simplify);
                  FStarC_TypeChecker_Cfg.erase_universes =
                    (uu___2.FStarC_TypeChecker_Cfg.erase_universes);
                  FStarC_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___2.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                  FStarC_TypeChecker_Cfg.reify_ =
                    (uu___2.FStarC_TypeChecker_Cfg.reify_);
                  FStarC_TypeChecker_Cfg.compress_uvars =
                    (uu___2.FStarC_TypeChecker_Cfg.compress_uvars);
                  FStarC_TypeChecker_Cfg.no_full_norm =
                    (uu___2.FStarC_TypeChecker_Cfg.no_full_norm);
                  FStarC_TypeChecker_Cfg.check_no_uvars =
                    (uu___2.FStarC_TypeChecker_Cfg.check_no_uvars);
                  FStarC_TypeChecker_Cfg.unmeta =
                    (uu___2.FStarC_TypeChecker_Cfg.unmeta);
                  FStarC_TypeChecker_Cfg.unascribe =
                    (uu___2.FStarC_TypeChecker_Cfg.unascribe);
                  FStarC_TypeChecker_Cfg.in_full_norm_request =
                    (uu___2.FStarC_TypeChecker_Cfg.in_full_norm_request);
                  FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___2.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStarC_TypeChecker_Cfg.nbe_step =
                    (uu___2.FStarC_TypeChecker_Cfg.nbe_step);
                  FStarC_TypeChecker_Cfg.for_extraction =
                    (uu___2.FStarC_TypeChecker_Cfg.for_extraction);
                  FStarC_TypeChecker_Cfg.unrefine =
                    (uu___2.FStarC_TypeChecker_Cfg.unrefine);
                  FStarC_TypeChecker_Cfg.default_univs_to_zero =
                    (uu___2.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                  FStarC_TypeChecker_Cfg.tactics =
                    (uu___2.FStarC_TypeChecker_Cfg.tactics);
                  FStarC_TypeChecker_Cfg.reduce_projections =
                    (uu___2.FStarC_TypeChecker_Cfg.reduce_projections)
                });
             FStarC_TypeChecker_Cfg.tcenv =
               (cfg.FStarC_TypeChecker_Cfg.tcenv);
             FStarC_TypeChecker_Cfg.debug =
               (cfg.FStarC_TypeChecker_Cfg.debug);
             FStarC_TypeChecker_Cfg.delta_level =
               (cfg.FStarC_TypeChecker_Cfg.delta_level);
             FStarC_TypeChecker_Cfg.primitive_steps =
               (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
             FStarC_TypeChecker_Cfg.strong =
               (cfg.FStarC_TypeChecker_Cfg.strong);
             FStarC_TypeChecker_Cfg.memoize_lazy =
               (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
             FStarC_TypeChecker_Cfg.normalize_pure_lets =
               (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
             FStarC_TypeChecker_Cfg.reifying =
               (cfg.FStarC_TypeChecker_Cfg.reifying);
             FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
               (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
           } in
         (FStarC_Effect.op_Colon_Equals weak_cfg_cache
            (FStar_Pervasives_Native.Some (cfg, cfg'));
          cfg'))
let whnf_cfg_cache :
  (FStarC_TypeChecker_Cfg.cfg * FStarC_TypeChecker_Cfg.cfg)
    FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let whnf_cfg (cfg : FStarC_TypeChecker_Cfg.cfg) : FStarC_TypeChecker_Cfg.cfg=
  if
    (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak &&
      (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.hnf
  then cfg
  else
    (let uu___ = FStarC_Effect.op_Bang whnf_cfg_cache in
     match uu___ with
     | FStar_Pervasives_Native.Some (cfg0, cfg0') when
         FStarC_Util.physical_equality cfg cfg0 -> cfg0'
     | uu___1 ->
         let cfg' =
           {
             FStarC_TypeChecker_Cfg.steps =
               (let uu___2 = cfg.FStarC_TypeChecker_Cfg.steps in
                {
                  FStarC_TypeChecker_Cfg.beta =
                    (uu___2.FStarC_TypeChecker_Cfg.beta);
                  FStarC_TypeChecker_Cfg.iota =
                    (uu___2.FStarC_TypeChecker_Cfg.iota);
                  FStarC_TypeChecker_Cfg.zeta =
                    (uu___2.FStarC_TypeChecker_Cfg.zeta);
                  FStarC_TypeChecker_Cfg.zeta_full =
                    (uu___2.FStarC_TypeChecker_Cfg.zeta_full);
                  FStarC_TypeChecker_Cfg.weak = true;
                  FStarC_TypeChecker_Cfg.hnf = true;
                  FStarC_TypeChecker_Cfg.primops =
                    (uu___2.FStarC_TypeChecker_Cfg.primops);
                  FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___2.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStarC_TypeChecker_Cfg.unfold_until =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_until);
                  FStarC_TypeChecker_Cfg.unfold_only =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_only);
                  FStarC_TypeChecker_Cfg.unfold_once =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_once);
                  FStarC_TypeChecker_Cfg.unfold_fully =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_fully);
                  FStarC_TypeChecker_Cfg.unfold_attr =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_attr);
                  FStarC_TypeChecker_Cfg.unfold_qual =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_qual);
                  FStarC_TypeChecker_Cfg.unfold_namespace =
                    (uu___2.FStarC_TypeChecker_Cfg.unfold_namespace);
                  FStarC_TypeChecker_Cfg.dont_unfold_attr =
                    (uu___2.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                  FStarC_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___2.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStarC_TypeChecker_Cfg.simplify =
                    (uu___2.FStarC_TypeChecker_Cfg.simplify);
                  FStarC_TypeChecker_Cfg.erase_universes =
                    (uu___2.FStarC_TypeChecker_Cfg.erase_universes);
                  FStarC_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___2.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                  FStarC_TypeChecker_Cfg.reify_ =
                    (uu___2.FStarC_TypeChecker_Cfg.reify_);
                  FStarC_TypeChecker_Cfg.compress_uvars =
                    (uu___2.FStarC_TypeChecker_Cfg.compress_uvars);
                  FStarC_TypeChecker_Cfg.no_full_norm =
                    (uu___2.FStarC_TypeChecker_Cfg.no_full_norm);
                  FStarC_TypeChecker_Cfg.check_no_uvars =
                    (uu___2.FStarC_TypeChecker_Cfg.check_no_uvars);
                  FStarC_TypeChecker_Cfg.unmeta =
                    (uu___2.FStarC_TypeChecker_Cfg.unmeta);
                  FStarC_TypeChecker_Cfg.unascribe =
                    (uu___2.FStarC_TypeChecker_Cfg.unascribe);
                  FStarC_TypeChecker_Cfg.in_full_norm_request =
                    (uu___2.FStarC_TypeChecker_Cfg.in_full_norm_request);
                  FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___2.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStarC_TypeChecker_Cfg.nbe_step =
                    (uu___2.FStarC_TypeChecker_Cfg.nbe_step);
                  FStarC_TypeChecker_Cfg.for_extraction =
                    (uu___2.FStarC_TypeChecker_Cfg.for_extraction);
                  FStarC_TypeChecker_Cfg.unrefine =
                    (uu___2.FStarC_TypeChecker_Cfg.unrefine);
                  FStarC_TypeChecker_Cfg.default_univs_to_zero =
                    (uu___2.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                  FStarC_TypeChecker_Cfg.tactics =
                    (uu___2.FStarC_TypeChecker_Cfg.tactics);
                  FStarC_TypeChecker_Cfg.reduce_projections =
                    (uu___2.FStarC_TypeChecker_Cfg.reduce_projections)
                });
             FStarC_TypeChecker_Cfg.tcenv =
               (cfg.FStarC_TypeChecker_Cfg.tcenv);
             FStarC_TypeChecker_Cfg.debug =
               (cfg.FStarC_TypeChecker_Cfg.debug);
             FStarC_TypeChecker_Cfg.delta_level =
               (cfg.FStarC_TypeChecker_Cfg.delta_level);
             FStarC_TypeChecker_Cfg.primitive_steps =
               (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
             FStarC_TypeChecker_Cfg.strong =
               (cfg.FStarC_TypeChecker_Cfg.strong);
             FStarC_TypeChecker_Cfg.memoize_lazy =
               (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
             FStarC_TypeChecker_Cfg.normalize_pure_lets =
               (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
             FStarC_TypeChecker_Cfg.reifying =
               (cfg.FStarC_TypeChecker_Cfg.reifying);
             FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
               (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
           } in
         (FStarC_Effect.op_Colon_Equals whnf_cfg_cache
            (FStar_Pervasives_Native.Some (cfg, cfg'));
          cfg'))
let read_memo (cfg : FStarC_TypeChecker_Cfg.cfg) (r : 'a cfg_memo) :
  'a FStar_Pervasives_Native.option=
  let read c =
    let uu___ = FStarC_Effect.op_Bang c in
    match uu___ with
    | FStar_Pervasives_Native.Some (cfg', a1) when
        if
          cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg ||
            (FStarC_Util.physical_equality cfg cfg')
        then true
        else cfg_equivalent cfg' cfg -> FStar_Pervasives_Native.Some a1
    | uu___1 -> FStar_Pervasives_Native.None in
  let uu___ = read (memo_cell cfg r) in
  match uu___ with
  | FStar_Pervasives_Native.Some a1 -> FStar_Pervasives_Native.Some a1
  | FStar_Pervasives_Native.None ->
      if cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg
      then FStarC_List.tryPick read (other_memo_cells cfg r)
      else FStar_Pervasives_Native.None
let set_memo (cfg : FStarC_TypeChecker_Cfg.cfg) (r : 'a cfg_memo) (t : 'a) :
  unit=
  if cfg.FStarC_TypeChecker_Cfg.memoize_lazy
  then
    ((let uu___1 =
        let uu___2 = read_memo cfg r in
        match uu___2 with
        | FStar_Pervasives_Native.Some v -> true
        | uu___3 -> false in
      if uu___1
      then
        FStarC_Effect.failwith "Unexpected set_memo: thunk already evaluated"
      else ());
     FStarC_Effect.op_Colon_Equals (memo_cell cfg r)
       (FStar_Pervasives_Native.Some (cfg, t)))
  else ()
let closure_to_string (uu___ : closure) : Prims.string=
  match uu___ with
  | Clos (env1, t, uu___1, uu___2) ->
      let uu___3 =
        FStarC_Class_Show.show FStarC_Class_Show.showable_nat
          (FStarC_List.length env1) in
      let uu___4 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
      FStarC_Format.fmt2 "(env=%s elts; %s)" uu___3 uu___4
  | Univ u ->
      let uu___1 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ u in
      Prims.strcat "Univ " uu___1
  | Dummy -> "dummy"
let showable_closure : closure FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = closure_to_string }
let showable_stack_elt : stack_elt FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Arg (c, uu___1, uu___2) ->
             let uu___3 = FStarC_Class_Show.show showable_closure c in
             FStarC_Format.fmt1 "Arg %s" uu___3
         | MemoLazy uu___1 -> "MemoLazy"
         | Abs (uu___1, bs, uu___2, uu___3, uu___4) ->
             let uu___5 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                 (FStarC_List.length bs) in
             FStarC_Format.fmt1 "Abs %s" uu___5
         | UnivArgs us ->
             let uu___1 =
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_tuple2
                    (FStarC_Class_Show.show_list
                       FStarC_Syntax_Print.showable_univ)
                    FStarC_Range_Ops.showable_range) us in
             Prims.strcat "UnivArgs " uu___1
         | Match uu___1 -> "Match"
         | App (uu___1, t, uu___2, uu___3) ->
             let uu___4 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
             FStarC_Format.fmt1 "App %s" uu___4
         | CBVApp (uu___1, t, uu___2, uu___3) ->
             let uu___4 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
             FStarC_Format.fmt1 "CBVApp %s" uu___4
         | Meta (uu___1, m, uu___2) -> "Meta"
         | Let uu___1 -> "Let")
  }
let is_empty (uu___ : 'uuuuu Prims.list) : Prims.bool=
  match uu___ with | [] -> true | uu___1 -> false
let lookup_bvar (env1 : env) (x : FStarC_Syntax_Syntax.bv) : closure=
  try
    (fun uu___ ->
       match () with
       | () ->
           (match FStarC_List.nth env1 x.FStarC_Syntax_Syntax.index with
            | (_1, _2, _3) -> _2)) ()
  with
  | uu___ ->
      let uu___1 =
        let uu___2 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv x in
        let uu___3 =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_list
               (FStarC_Class_Show.show_tuple3
                  (FStarC_Class_Show.show_option
                     FStarC_Syntax_Print.showable_binder) showable_closure
                  (showable_memo
                     (FStarC_Class_Show.show_list
                        FStarC_Syntax_Print.showable_subst_elt)))) env1 in
        FStarC_Format.fmt2 "Failed to find %s\nEnv is %s\n" uu___2 uu___3 in
      FStarC_Effect.failwith uu___1
let downgrade_ghost_effect_name (l : FStarC_Ident.lident) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  if FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_Ghost_lid
  then FStar_Pervasives_Native.Some FStarC_Parser_Const.effect_Pure_lid
  else
    if FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_GTot_lid
    then FStar_Pervasives_Native.Some FStarC_Parser_Const.effect_Tot_lid
    else
      if FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_GHOST_lid
      then FStar_Pervasives_Native.Some FStarC_Parser_Const.effect_PURE_lid
      else FStar_Pervasives_Native.None
let norm_universe (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (u : FStarC_Syntax_Syntax.universe) : FStarC_Syntax_Syntax.universe=
  let norm_univs_for_max us =
    let us1 = FStarC_Util.sort_with FStarC_Syntax_Util.compare_univs us in
    let uu___ =
      FStarC_List.fold_left
        (fun uu___1 u1 ->
           match uu___1 with
           | (cur_kernel, cur_max, out) ->
               let uu___2 = FStarC_Syntax_Util.univ_kernel u1 in
               (match uu___2 with
                | (k_u, n) ->
                    let uu___3 = FStarC_Syntax_Util.eq_univs cur_kernel k_u in
                    if uu___3
                    then (cur_kernel, u1, out)
                    else (k_u, u1, (cur_max :: out))))
        (FStarC_Syntax_Syntax.U_zero, FStarC_Syntax_Syntax.U_zero, []) us1 in
    match uu___ with | (uu___1, u1, out) -> FStarC_List.rev (u1 :: out) in
  let rec aux u1 =
    let u2 = FStarC_Syntax_Subst.compress_univ u1 in
    match u2 with
    | FStarC_Syntax_Syntax.U_bvar x ->
        let vo =
          try
            (fun uu___ ->
               match () with
               | () ->
                   FStar_Pervasives_Native.Some
                     ((match FStarC_List.nth env1 x with | (_1, _2, _3) -> _2)))
              ()
          with | uu___ -> FStar_Pervasives_Native.None in
        (match vo with
         | FStar_Pervasives_Native.Some (Univ u3) ->
             ((let uu___1 = FStarC_Effect.op_Bang dbg_univ_norm in
               if uu___1
               then
                 let uu___2 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                     u3 in
                 FStarC_Format.print1 "Univ (in norm_universe): %s\n" uu___2
               else ());
              aux u3)
         | FStar_Pervasives_Native.Some (Dummy) -> [u2]
         | FStar_Pervasives_Native.Some uu___ ->
             if
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.allow_unbound_universes
             then [FStarC_Syntax_Syntax.U_unknown]
             else
               (let uu___1 =
                  let uu___2 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int x in
                  FStarC_Format.fmt1
                    "Impossible: universe variable u@%s bound to a term"
                    uu___2 in
                FStarC_Effect.failwith uu___1)
         | FStar_Pervasives_Native.None ->
             if
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.allow_unbound_universes
             then [FStarC_Syntax_Syntax.U_unknown]
             else
               (let uu___ =
                  let uu___1 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int x in
                  Prims.strcat "Universe variable not found: u@" uu___1 in
                FStarC_Effect.failwith uu___))
    | FStarC_Syntax_Syntax.U_unif uu___ when
        (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.default_univs_to_zero
        -> [FStarC_Syntax_Syntax.U_zero]
    | FStarC_Syntax_Syntax.U_unif uu___ when
        (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.check_no_uvars
        ->
        let uu___1 =
          let uu___2 =
            FStarC_Range_Ops.string_of_range
              (FStarC_TypeChecker_Env.get_range
                 cfg.FStarC_TypeChecker_Cfg.tcenv) in
          let uu___3 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ u2 in
          FStarC_Format.fmt2
            "(%s) CheckNoUvars: unexpected universes variable remains: %s"
            uu___2 uu___3 in
        FStarC_Effect.failwith uu___1
    | FStarC_Syntax_Syntax.U_zero -> [u2]
    | FStarC_Syntax_Syntax.U_unif uu___ -> [u2]
    | FStarC_Syntax_Syntax.U_name uu___ -> [u2]
    | FStarC_Syntax_Syntax.U_unknown -> [u2]
    | FStarC_Syntax_Syntax.U_max [] -> [FStarC_Syntax_Syntax.U_zero]
    | FStarC_Syntax_Syntax.U_max us ->
        let us1 =
          let uu___ = FStarC_List.collect aux us in norm_univs_for_max uu___ in
        (match us1 with
         | u_k::hd::rest ->
             let rest1 = hd :: rest in
             let uu___ = FStarC_Syntax_Util.univ_kernel u_k in
             (match uu___ with
              | (FStarC_Syntax_Syntax.U_zero, n) ->
                  let uu___1 =
                    FStarC_List.for_all
                      (fun u3 ->
                         let uu___2 = FStarC_Syntax_Util.univ_kernel u3 in
                         match uu___2 with | (uu___3, m) -> n <= m) rest1 in
                  if uu___1 then rest1 else us1
              | uu___1 -> us1)
         | uu___ -> us1)
    | FStarC_Syntax_Syntax.U_succ u3 ->
        let uu___ = aux u3 in
        FStarC_List.map (fun uu___1 -> FStarC_Syntax_Syntax.U_succ uu___1)
          uu___ in
  if
    (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.erase_universes
  then FStarC_Syntax_Syntax.U_unknown
  else
    (let uu___ = aux u in
     match uu___ with
     | [] -> FStarC_Syntax_Syntax.U_zero
     | (FStarC_Syntax_Syntax.U_zero)::[] -> FStarC_Syntax_Syntax.U_zero
     | (FStarC_Syntax_Syntax.U_zero)::u1::[] -> u1
     | (FStarC_Syntax_Syntax.U_zero)::us -> FStarC_Syntax_Syntax.U_max us
     | u1::[] -> u1
     | us -> FStarC_Syntax_Syntax.U_max us)
let memo_or (m : 'a FStarC_Syntax_Syntax.memo) (f : unit -> 'a) : 'a=
  let uu___ = FStarC_Effect.op_Bang m in
  match uu___ with
  | FStar_Pervasives_Native.Some v -> v
  | FStar_Pervasives_Native.None ->
      let v = f () in
      (FStarC_Effect.op_Colon_Equals m (FStar_Pervasives_Native.Some v); v)
let rec env_subst (env1 : env) : FStarC_Syntax_Syntax.subst_t=
  let compute uu___ =
    let uu___1 =
      FStarC_List.fold_left
        (fun uu___2 uu___3 ->
           match (uu___2, uu___3) with
           | ((s, i), (uu___4, c, uu___5)) ->
               (match c with
                | Clos (e, t, memo, fix) ->
                    let es = env_subst e in
                    let t1 =
                      let uu___6 = FStarC_Syntax_Subst.subst es t in
                      FStarC_Syntax_Subst.compress uu___6 in
                    (((FStarC_Syntax_Syntax.DT (i, t1)) :: s),
                      (i + Prims.int_one))
                | Univ u ->
                    (((FStarC_Syntax_Syntax.UN (i, u)) :: s),
                      (i + Prims.int_one))
                | Dummy -> (s, (i + Prims.int_one)))) ([], Prims.int_zero)
        env1 in
    match uu___1 with | (s, uu___2) -> s in
  match env1 with
  | [] -> []
  | (uu___, uu___1, memo)::uu___2 ->
      let uu___3 = FStarC_Effect.op_Bang memo in
      (match uu___3 with
       | FStar_Pervasives_Native.Some s -> s
       | FStar_Pervasives_Native.None ->
           let s = compute () in
           (FStarC_Effect.op_Colon_Equals memo
              (FStar_Pervasives_Native.Some s);
            s))
let filter_out_lcomp_cflags (flags : FStarC_Syntax_Syntax.cflag Prims.list) :
  FStarC_Syntax_Syntax.cflag Prims.list=
  FStarC_List.filter
    (fun uu___ ->
       match uu___ with
       | FStarC_Syntax_Syntax.DECREASES uu___1 -> false
       | uu___1 -> true) flags
let default_univ_uvars_to_zero (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  FStarC_Syntax_Visit.visit_term_univs false (fun t1 -> t1)
    (fun u ->
       match u with
       | FStarC_Syntax_Syntax.U_unif uu___ -> FStarC_Syntax_Syntax.U_zero
       | uu___ -> u) t
let _erase_universes (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  FStarC_Syntax_Visit.visit_term_univs false (fun t1 -> t1)
    (fun u -> FStarC_Syntax_Syntax.U_unknown) t
let closure_as_term (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  FStarC_TypeChecker_Cfg.log cfg
    (fun uu___1 ->
       let uu___2 =
         FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t in
       let uu___3 =
         FStarC_Class_Show.show
           (FStarC_Class_Show.show_list
              (FStarC_Class_Show.show_tuple3
                 (FStarC_Class_Show.show_option
                    FStarC_Syntax_Print.showable_binder) showable_closure
                 (showable_memo
                    (FStarC_Class_Show.show_list
                       FStarC_Syntax_Print.showable_subst_elt)))) env1 in
       let uu___4 =
         FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
       FStarC_Format.print3 ">>> %s (env=%s)\nClosure_as_term %s\n" uu___2
         uu___3 uu___4);
  (let es = env_subst env1 in
   let t1 = FStarC_Syntax_Subst.subst es t in
   let t2 =
     if
       (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.erase_universes
     then _erase_universes t1
     else
       if
         (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.default_univs_to_zero
       then default_univ_uvars_to_zero t1
       else t1 in
   let t3 = FStarC_Syntax_Subst.compress t2 in
   FStarC_TypeChecker_Cfg.log cfg
     (fun uu___2 ->
        let uu___3 =
          FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t3 in
        let uu___4 =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_list
               (FStarC_Class_Show.show_tuple3
                  (FStarC_Class_Show.show_option
                     FStarC_Syntax_Print.showable_binder) showable_closure
                  (showable_memo
                     (FStarC_Class_Show.show_list
                        FStarC_Syntax_Print.showable_subst_elt)))) env1 in
        let uu___5 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t3 in
        FStarC_Format.print3 ">>> %s (env=%s)\nClosure_as_term RESULT %s\n"
          uu___3 uu___4 uu___5);
   t3)
let unembed_binder_knot :
  FStarC_Syntax_Syntax.binder FStarC_Syntax_Embeddings_Base.embedding
    FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let unembed_binder (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.binder FStar_Pervasives_Native.option=
  let uu___ = FStarC_Effect.op_Bang unembed_binder_knot in
  match uu___ with
  | FStar_Pervasives_Native.Some e ->
      FStarC_Syntax_Embeddings_Base.try_unembed e t
        FStarC_Syntax_Embeddings_Base.id_norm_cb
  | FStar_Pervasives_Native.None ->
      (FStarC_Errors.log_issue (FStarC_Syntax_Syntax.has_range_syntax ()) t
         FStarC_Errors_Codes.Warning_UnembedBinderKnot ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
         (Obj.magic "unembed_binder_knot is unset!");
       FStar_Pervasives_Native.None)
let mk_psc_subst (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env) :
  FStarC_Syntax_Syntax.subst_elt Prims.list=
  FStarC_List.fold_right
    (fun uu___ subst ->
       match uu___ with
       | (binder_opt, closure1, uu___1) ->
           (match (binder_opt, closure1) with
            | (FStar_Pervasives_Native.Some b, Clos
               (env2, term, uu___2, uu___3)) ->
                let bv = b.FStarC_Syntax_Syntax.binder_bv in
                let uu___4 =
                  let uu___5 =
                    FStarC_Syntax_Util.is_constructed_typ
                      bv.FStarC_Syntax_Syntax.sort
                      FStarC_Parser_Const.binder_lid in
                  Prims.not uu___5 in
                if uu___4
                then subst
                else
                  (let term1 = closure_as_term cfg env2 term in
                   let uu___5 = unembed_binder term1 in
                   match uu___5 with
                   | FStar_Pervasives_Native.None -> subst
                   | FStar_Pervasives_Native.Some x ->
                       let b1 =
                         let uu___6 =
                           let uu___7 =
                             FStarC_Syntax_Subst.subst subst
                               (x.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                           {
                             FStarC_Syntax_Syntax.ppname =
                               (bv.FStarC_Syntax_Syntax.ppname);
                             FStarC_Syntax_Syntax.index =
                               (bv.FStarC_Syntax_Syntax.index);
                             FStarC_Syntax_Syntax.sort = uu___7
                           } in
                         FStarC_Syntax_Syntax.freshen_bv uu___6 in
                       let b_for_x =
                         let uu___6 =
                           let uu___7 = FStarC_Syntax_Syntax.bv_to_name b1 in
                           ((x.FStarC_Syntax_Syntax.binder_bv), uu___7) in
                         FStarC_Syntax_Syntax.NT uu___6 in
                       let subst1 =
                         FStarC_List.filter
                           (fun uu___6 ->
                              match uu___6 with
                              | FStarC_Syntax_Syntax.NT
                                  (uu___7,
                                   {
                                     FStarC_Syntax_Syntax.n =
                                       FStarC_Syntax_Syntax.Tm_name b';
                                     FStarC_Syntax_Syntax.pos = uu___8;
                                     FStarC_Syntax_Syntax.hash_code = uu___9;_})
                                  ->
                                  Prims.not
                                    (FStarC_Ident.ident_equals
                                       b1.FStarC_Syntax_Syntax.ppname
                                       b'.FStarC_Syntax_Syntax.ppname)
                              | uu___7 -> true) subst in
                       b_for_x :: subst1)
            | uu___2 -> subst)) env1 []
let reduce_primops (norm_cb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (tm : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax) :
  (FStarC_Syntax_Syntax.term * Prims.bool)=
  if
    Prims.not
      (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.primops
  then (tm, false)
  else
    (let uu___ = FStarC_Syntax_Util.head_and_args_full tm in
     match uu___ with
     | (head, args) ->
         let uu___1 =
           let head1 =
             let uu___2 = FStarC_Syntax_Util.unmeta head in
             FStarC_Syntax_Subst.compress uu___2 in
           match head1.FStarC_Syntax_Syntax.n with
           | FStarC_Syntax_Syntax.Tm_uinst (fv, us) -> (fv, us)
           | uu___2 -> (head1, []) in
         (match uu___1 with
          | (head_term, universes) ->
              (match head_term.FStarC_Syntax_Syntax.n with
               | FStarC_Syntax_Syntax.Tm_fvar fv ->
                   let uu___2 = FStarC_TypeChecker_Cfg.find_prim_step cfg fv in
                   (match uu___2 with
                    | FStar_Pervasives_Native.Some prim_step when
                        prim_step.FStarC_TypeChecker_Primops_Base.strong_reduction_ok
                          || (Prims.not cfg.FStarC_TypeChecker_Cfg.strong)
                        ->
                        let l = FStarC_List.length args in
                        if
                          l < prim_step.FStarC_TypeChecker_Primops_Base.arity
                        then
                          (FStarC_TypeChecker_Cfg.log_primops cfg
                             (fun uu___4 ->
                                let uu___5 =
                                  FStarC_Class_Show.show
                                    FStarC_Ident.showable_lident
                                    prim_step.FStarC_TypeChecker_Primops_Base.name in
                                let uu___6 =
                                  FStarC_Class_Show.show
                                    FStarC_Class_Show.showable_nat l in
                                let uu___7 =
                                  FStarC_Class_Show.show
                                    FStarC_Class_Show.showable_int
                                    prim_step.FStarC_TypeChecker_Primops_Base.arity in
                                FStarC_Format.print3
                                  "primop: found partially applied %s (%s/%s args)\n"
                                  uu___5 uu___6 uu___7);
                           (tm, false))
                        else
                          (let uu___3 =
                             if
                               l =
                                 prim_step.FStarC_TypeChecker_Primops_Base.arity
                             then (args, [])
                             else
                               FStarC_List.splitAt
                                 prim_step.FStarC_TypeChecker_Primops_Base.arity
                                 args in
                           match uu___3 with
                           | (args_1, args_2) ->
                               (FStarC_TypeChecker_Cfg.log_primops cfg
                                  (fun uu___5 ->
                                     let uu___6 =
                                       FStarC_Class_Show.show
                                         FStarC_Syntax_Print.showable_term tm in
                                     FStarC_Format.print1
                                       "primop: trying to reduce <%s>\n"
                                       uu___6);
                                (let psc =
                                   {
                                     FStarC_TypeChecker_Primops_Base.psc_range
                                       = (head.FStarC_Syntax_Syntax.pos);
                                     FStarC_TypeChecker_Primops_Base.psc_subst
                                       =
                                       (fun uu___5 ->
                                          if
                                            prim_step.FStarC_TypeChecker_Primops_Base.requires_binder_substitution
                                          then mk_psc_subst cfg env1
                                          else [])
                                   } in
                                 let r =
                                   prim_step.FStarC_TypeChecker_Primops_Base.interpretation
                                     psc norm_cb universes args_1 in
                                 match r with
                                 | FStar_Pervasives_Native.None ->
                                     (FStarC_TypeChecker_Cfg.log_primops cfg
                                        (fun uu___6 ->
                                           let uu___7 =
                                             FStarC_Class_Show.show
                                               FStarC_Syntax_Print.showable_term
                                               tm in
                                           FStarC_Format.print1
                                             "primop: <%s> did not reduce\n"
                                             uu___7);
                                      (tm, false))
                                 | FStar_Pervasives_Native.Some reduced ->
                                     (FStarC_TypeChecker_Cfg.log_primops cfg
                                        (fun uu___6 ->
                                           let uu___7 =
                                             FStarC_Class_Show.show
                                               FStarC_Syntax_Print.showable_term
                                               tm in
                                           let uu___8 =
                                             FStarC_Class_Show.show
                                               FStarC_Syntax_Print.showable_term
                                               reduced in
                                           FStarC_Format.print2
                                             "primop: <%s> reduced to  %s\n"
                                             uu___7 uu___8);
                                      (let uu___6 =
                                         FStarC_Syntax_Util.mk_app reduced
                                           args_2 in
                                       (uu___6,
                                         (prim_step.FStarC_TypeChecker_Primops_Base.renorm_after)))))))
                    | FStar_Pervasives_Native.Some uu___3 ->
                        (FStarC_TypeChecker_Cfg.log_primops cfg
                           (fun uu___5 ->
                              let uu___6 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_term tm in
                              FStarC_Format.print1
                                "primop: not reducing <%s> since we're doing strong reduction\n"
                                uu___6);
                         (tm, false))
                    | FStar_Pervasives_Native.None -> (tm, false))
               | FStarC_Syntax_Syntax.Tm_constant
                   (FStarC_Const.Const_range_of) when
                   Prims.not cfg.FStarC_TypeChecker_Cfg.strong ->
                   (FStarC_TypeChecker_Cfg.log_primops cfg
                      (fun uu___3 ->
                         let uu___4 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term tm in
                         FStarC_Format.print1 "primop: reducing <%s>\n"
                           uu___4);
                    (match args with
                     | (a1, uu___3)::[] ->
                         let uu___4 =
                           FStarC_TypeChecker_Primops_Base.embed_simple
                             FStarC_Syntax_Embeddings.e_range
                             a1.FStarC_Syntax_Syntax.pos
                             tm.FStarC_Syntax_Syntax.pos in
                         (uu___4, false)
                     | uu___3 -> (tm, false)))
               | FStarC_Syntax_Syntax.Tm_constant
                   (FStarC_Const.Const_set_range_of) when
                   Prims.not cfg.FStarC_TypeChecker_Cfg.strong ->
                   (FStarC_TypeChecker_Cfg.log_primops cfg
                      (fun uu___3 ->
                         let uu___4 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term tm in
                         FStarC_Format.print1 "primop: reducing <%s>\n"
                           uu___4);
                    (match args with
                     | (t, uu___3)::(r, uu___4)::[] ->
                         let uu___5 =
                           FStarC_TypeChecker_Primops_Base.try_unembed_simple
                             FStarC_Syntax_Embeddings.e_range r in
                         (match uu___5 with
                          | FStar_Pervasives_Native.Some rng ->
                              let uu___6 =
                                FStarC_Syntax_Subst.set_use_range rng t in
                              (uu___6, false)
                          | FStar_Pervasives_Native.None -> (tm, false))
                     | uu___3 -> (tm, false)))
               | uu___2 -> (tm, false))))
let reduce_equality (norm_cb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (cfg : FStarC_TypeChecker_Cfg.cfg) (tm : env) :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    (FStarC_Syntax_Syntax.term * Prims.bool)=
  let uu___ =
    let uu___1 =
      FStarC_TypeChecker_Cfg.simplification_steps
        cfg.FStarC_TypeChecker_Cfg.tcenv in
    {
      FStarC_TypeChecker_Cfg.steps =
        {
          FStarC_TypeChecker_Cfg.beta =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.beta);
          FStarC_TypeChecker_Cfg.iota =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.iota);
          FStarC_TypeChecker_Cfg.zeta =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.zeta);
          FStarC_TypeChecker_Cfg.zeta_full =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.zeta_full);
          FStarC_TypeChecker_Cfg.weak =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.weak);
          FStarC_TypeChecker_Cfg.hnf =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.hnf);
          FStarC_TypeChecker_Cfg.primops = true;
          FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
          FStarC_TypeChecker_Cfg.unfold_until =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unfold_until);
          FStarC_TypeChecker_Cfg.unfold_only =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unfold_only);
          FStarC_TypeChecker_Cfg.unfold_once =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unfold_once);
          FStarC_TypeChecker_Cfg.unfold_fully =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unfold_fully);
          FStarC_TypeChecker_Cfg.unfold_attr =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unfold_attr);
          FStarC_TypeChecker_Cfg.unfold_qual =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unfold_qual);
          FStarC_TypeChecker_Cfg.unfold_namespace =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unfold_namespace);
          FStarC_TypeChecker_Cfg.dont_unfold_attr =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.dont_unfold_attr);
          FStarC_TypeChecker_Cfg.pure_subterms_within_computations =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
          FStarC_TypeChecker_Cfg.simplify =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.simplify);
          FStarC_TypeChecker_Cfg.erase_universes =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.erase_universes);
          FStarC_TypeChecker_Cfg.allow_unbound_universes =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.allow_unbound_universes);
          FStarC_TypeChecker_Cfg.reify_ =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.reify_);
          FStarC_TypeChecker_Cfg.compress_uvars =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.compress_uvars);
          FStarC_TypeChecker_Cfg.no_full_norm =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.no_full_norm);
          FStarC_TypeChecker_Cfg.check_no_uvars =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.check_no_uvars);
          FStarC_TypeChecker_Cfg.unmeta =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unmeta);
          FStarC_TypeChecker_Cfg.unascribe =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unascribe);
          FStarC_TypeChecker_Cfg.in_full_norm_request =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.in_full_norm_request);
          FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
          FStarC_TypeChecker_Cfg.nbe_step =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.nbe_step);
          FStarC_TypeChecker_Cfg.for_extraction =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.for_extraction);
          FStarC_TypeChecker_Cfg.unrefine =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unrefine);
          FStarC_TypeChecker_Cfg.default_univs_to_zero =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.default_univs_to_zero);
          FStarC_TypeChecker_Cfg.tactics =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.tactics);
          FStarC_TypeChecker_Cfg.reduce_projections =
            (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.reduce_projections)
        };
      FStarC_TypeChecker_Cfg.tcenv = (cfg.FStarC_TypeChecker_Cfg.tcenv);
      FStarC_TypeChecker_Cfg.debug = (cfg.FStarC_TypeChecker_Cfg.debug);
      FStarC_TypeChecker_Cfg.delta_level =
        (cfg.FStarC_TypeChecker_Cfg.delta_level);
      FStarC_TypeChecker_Cfg.primitive_steps = uu___1;
      FStarC_TypeChecker_Cfg.strong = (cfg.FStarC_TypeChecker_Cfg.strong);
      FStarC_TypeChecker_Cfg.memoize_lazy =
        (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
      FStarC_TypeChecker_Cfg.normalize_pure_lets =
        (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
      FStarC_TypeChecker_Cfg.reifying = (cfg.FStarC_TypeChecker_Cfg.reifying);
      FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
        (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
    } in
  reduce_primops norm_cb uu___ tm
let should_consider_norm_requests (cfg : FStarC_TypeChecker_Cfg.cfg) :
  Prims.bool=
  (Prims.not
     (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.no_full_norm)
    &&
    (Prims.not
       (FStarC_Ident.lid_equals
          (cfg.FStarC_TypeChecker_Cfg.tcenv).FStarC_TypeChecker_Env.curmodule
          FStarC_Parser_Const.prims_lid))
let is_nbe_request (s : FStarC_TypeChecker_Env.step Prims.list) : Prims.bool=
  FStarC_Util.for_some
    (FStarC_Class_Deq.op_Equals_Question FStarC_TypeChecker_Env.deq_step
       FStarC_TypeChecker_Env.NBE) s
let nbe_eval (cfg : FStarC_TypeChecker_Cfg.cfg)
  (s : FStarC_TypeChecker_Env.steps) (tm : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  let delta_level =
    let uu___ =
      FStarC_Util.for_some
        (fun uu___1 ->
           match uu___1 with
           | FStarC_TypeChecker_Env.UnfoldUntil uu___2 -> true
           | FStarC_TypeChecker_Env.UnfoldOnly uu___2 -> true
           | FStarC_TypeChecker_Env.UnfoldFully uu___2 -> true
           | uu___2 -> false) s in
    if uu___
    then [FStarC_TypeChecker_Env.Unfold FStarC_Syntax_Syntax.delta_constant]
    else [FStarC_TypeChecker_Env.NoDelta] in
  FStarC_TypeChecker_Cfg.log_nbe cfg
    (fun uu___1 ->
       let uu___2 =
         FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tm in
       FStarC_Format.print1 "Invoking NBE with  %s\n" uu___2);
  (let tm_norm =
     (FStarC_TypeChecker_Cfg.cfg_env cfg).FStarC_TypeChecker_Env.nbe s
       cfg.FStarC_TypeChecker_Cfg.tcenv tm in
   FStarC_TypeChecker_Cfg.log_nbe cfg
     (fun uu___2 ->
        let uu___3 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tm_norm in
        FStarC_Format.print1 "Result of NBE is  %s\n" uu___3);
   tm_norm)
let firstn (k : Prims.int) (l : 'uuuuu Prims.list) :
  ('uuuuu Prims.list * 'uuuuu Prims.list)=
  if (FStarC_List.length l) < k then (l, []) else FStarC_Util.first_N k l
let should_reify (cfg : FStarC_TypeChecker_Cfg.cfg)
  (stack1 : stack_elt Prims.list) : Prims.bool=
  let rec drop_irrel uu___ =
    match uu___ with
    | (MemoLazy uu___1)::s -> drop_irrel s
    | (UnivArgs uu___1)::s -> drop_irrel s
    | s -> s in
  match drop_irrel stack1 with
  | (App
      (uu___,
       {
         FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
           (FStarC_Const.Const_reify uu___1);
         FStarC_Syntax_Syntax.pos = uu___2;
         FStarC_Syntax_Syntax.hash_code = uu___3;_},
       uu___4, uu___5))::uu___6
      -> (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.reify_
  | uu___ -> false
let rec maybe_weakly_reduced
  (tm : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax) : Prims.bool=
  let aux_comp c =
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.GTotal t -> maybe_weakly_reduced t
    | FStarC_Syntax_Syntax.Total t -> maybe_weakly_reduced t
    | FStarC_Syntax_Syntax.Comp ct ->
        let uu___ =
          let uu___1 =
            maybe_weakly_reduced ct.FStarC_Syntax_Syntax.result_typ in
          if uu___1
          then true
          else maybe_weakly_reduced ct.FStarC_Syntax_Syntax.comp_pre in
        if uu___
        then true
        else maybe_weakly_reduced ct.FStarC_Syntax_Syntax.comp_post in
  let t = FStarC_Syntax_Subst.compress tm in
  match t.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_delayed uu___ ->
      FStarC_Effect.failwith "Impossible"
  | FStarC_Syntax_Syntax.Tm_name uu___ -> false
  | FStarC_Syntax_Syntax.Tm_uvar uu___ -> false
  | FStarC_Syntax_Syntax.Tm_type uu___ -> false
  | FStarC_Syntax_Syntax.Tm_bvar uu___ -> false
  | FStarC_Syntax_Syntax.Tm_fvar uu___ -> false
  | FStarC_Syntax_Syntax.Tm_constant uu___ -> false
  | FStarC_Syntax_Syntax.Tm_lazy uu___ -> false
  | FStarC_Syntax_Syntax.Tm_unknown -> false
  | FStarC_Syntax_Syntax.Tm_uinst uu___ -> false
  | FStarC_Syntax_Syntax.Tm_quoted uu___ -> false
  | FStarC_Syntax_Syntax.Tm_let uu___ -> true
  | FStarC_Syntax_Syntax.Tm_abs uu___ -> true
  | FStarC_Syntax_Syntax.Tm_arrow uu___ -> true
  | FStarC_Syntax_Syntax.Tm_refine uu___ -> true
  | FStarC_Syntax_Syntax.Tm_match uu___ -> true
  | FStarC_Syntax_Syntax.Tm_app uu___ ->
      let uu___1 = FStarC_Syntax_Util.head_and_args_full t in
      (match uu___1 with
       | (hd, args) ->
           let uu___2 = maybe_weakly_reduced hd in
           if uu___2
           then true
           else
             FStarC_Util.for_some
               (fun uu___3 ->
                  match uu___3 with | (a, uu___4) -> maybe_weakly_reduced a)
               args)
  | FStarC_Syntax_Syntax.Tm_ascribed
      { FStarC_Syntax_Syntax.tm = t1; FStarC_Syntax_Syntax.asc = asc;
        FStarC_Syntax_Syntax.eff_opt = uu___;_}
      ->
      let uu___1 = maybe_weakly_reduced t1 in
      if uu___1
      then true
      else
        (let uu___2 = asc in
         match uu___2 with
         | (asc_tc, asc_tac, uu___3) ->
             let uu___4 =
               match asc_tc with
               | FStar_Pervasives.Inl t2 -> maybe_weakly_reduced t2
               | FStar_Pervasives.Inr c2 -> aux_comp c2 in
             if uu___4
             then true
             else
               (match asc_tac with
                | FStar_Pervasives_Native.None -> false
                | FStar_Pervasives_Native.Some tac ->
                    maybe_weakly_reduced tac))
  | FStarC_Syntax_Syntax.Tm_meta
      { FStarC_Syntax_Syntax.tm2 = t1; FStarC_Syntax_Syntax.meta = m;_} ->
      let uu___ = maybe_weakly_reduced t1 in
      if uu___
      then true
      else
        (match m with
         | FStarC_Syntax_Syntax.Meta_pattern (uu___1, args) ->
             FStarC_Util.for_some
               (FStarC_Util.for_some
                  (fun uu___2 ->
                     match uu___2 with
                     | (a, uu___3) -> maybe_weakly_reduced a)) args
         | FStarC_Syntax_Syntax.Meta_monadic_lift (uu___1, uu___2, t') ->
             maybe_weakly_reduced t'
         | FStarC_Syntax_Syntax.Meta_monadic (uu___1, t') ->
             maybe_weakly_reduced t'
         | FStarC_Syntax_Syntax.Meta_labeled uu___1 -> false
         | FStarC_Syntax_Syntax.Meta_desugared uu___1 -> false
         | FStarC_Syntax_Syntax.Meta_named uu___1 -> false)
let decide_unfolding (cfg : FStarC_TypeChecker_Cfg.cfg) (stack1 : stack)
  (fv : FStarC_Syntax_Syntax.fv) (qninfo : FStarC_TypeChecker_Env.qninfo) :
  (FStarC_TypeChecker_Cfg.cfg FStar_Pervasives_Native.option * stack)
    FStar_Pervasives_Native.option=
  let res =
    FStarC_TypeChecker_Normalize_Unfolding.should_unfold false cfg
      (fun cfg1 -> should_reify cfg1 stack1) fv qninfo in
  match res with
  | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_no ->
      FStar_Pervasives_Native.None
  | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_yes ->
      FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None, stack1)
  | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_once ->
      let uu___ =
        (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_once in
      (match uu___ with
       | FStar_Pervasives_Native.Some once ->
           let cfg' =
             let uu___1 =
               let uu___2 = cfg.FStarC_TypeChecker_Cfg.steps in
               let uu___3 =
                 let uu___4 =
                   FStarC_List.filter
                     (fun lid ->
                        Prims.not (FStarC_Syntax_Syntax.fv_eq_lid fv lid))
                     once in
                 FStar_Pervasives_Native.Some uu___4 in
               {
                 FStarC_TypeChecker_Cfg.beta =
                   (uu___2.FStarC_TypeChecker_Cfg.beta);
                 FStarC_TypeChecker_Cfg.iota =
                   (uu___2.FStarC_TypeChecker_Cfg.iota);
                 FStarC_TypeChecker_Cfg.zeta =
                   (uu___2.FStarC_TypeChecker_Cfg.zeta);
                 FStarC_TypeChecker_Cfg.zeta_full =
                   (uu___2.FStarC_TypeChecker_Cfg.zeta_full);
                 FStarC_TypeChecker_Cfg.weak =
                   (uu___2.FStarC_TypeChecker_Cfg.weak);
                 FStarC_TypeChecker_Cfg.hnf =
                   (uu___2.FStarC_TypeChecker_Cfg.hnf);
                 FStarC_TypeChecker_Cfg.primops =
                   (uu___2.FStarC_TypeChecker_Cfg.primops);
                 FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___2.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStarC_TypeChecker_Cfg.unfold_until =
                   (uu___2.FStarC_TypeChecker_Cfg.unfold_until);
                 FStarC_TypeChecker_Cfg.unfold_only =
                   (uu___2.FStarC_TypeChecker_Cfg.unfold_only);
                 FStarC_TypeChecker_Cfg.unfold_once = uu___3;
                 FStarC_TypeChecker_Cfg.unfold_fully =
                   (uu___2.FStarC_TypeChecker_Cfg.unfold_fully);
                 FStarC_TypeChecker_Cfg.unfold_attr =
                   (uu___2.FStarC_TypeChecker_Cfg.unfold_attr);
                 FStarC_TypeChecker_Cfg.unfold_qual =
                   (uu___2.FStarC_TypeChecker_Cfg.unfold_qual);
                 FStarC_TypeChecker_Cfg.unfold_namespace =
                   (uu___2.FStarC_TypeChecker_Cfg.unfold_namespace);
                 FStarC_TypeChecker_Cfg.dont_unfold_attr =
                   (uu___2.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                 FStarC_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___2.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStarC_TypeChecker_Cfg.simplify =
                   (uu___2.FStarC_TypeChecker_Cfg.simplify);
                 FStarC_TypeChecker_Cfg.erase_universes =
                   (uu___2.FStarC_TypeChecker_Cfg.erase_universes);
                 FStarC_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___2.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                 FStarC_TypeChecker_Cfg.reify_ =
                   (uu___2.FStarC_TypeChecker_Cfg.reify_);
                 FStarC_TypeChecker_Cfg.compress_uvars =
                   (uu___2.FStarC_TypeChecker_Cfg.compress_uvars);
                 FStarC_TypeChecker_Cfg.no_full_norm =
                   (uu___2.FStarC_TypeChecker_Cfg.no_full_norm);
                 FStarC_TypeChecker_Cfg.check_no_uvars =
                   (uu___2.FStarC_TypeChecker_Cfg.check_no_uvars);
                 FStarC_TypeChecker_Cfg.unmeta =
                   (uu___2.FStarC_TypeChecker_Cfg.unmeta);
                 FStarC_TypeChecker_Cfg.unascribe =
                   (uu___2.FStarC_TypeChecker_Cfg.unascribe);
                 FStarC_TypeChecker_Cfg.in_full_norm_request =
                   (uu___2.FStarC_TypeChecker_Cfg.in_full_norm_request);
                 FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___2.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStarC_TypeChecker_Cfg.nbe_step =
                   (uu___2.FStarC_TypeChecker_Cfg.nbe_step);
                 FStarC_TypeChecker_Cfg.for_extraction =
                   (uu___2.FStarC_TypeChecker_Cfg.for_extraction);
                 FStarC_TypeChecker_Cfg.unrefine =
                   (uu___2.FStarC_TypeChecker_Cfg.unrefine);
                 FStarC_TypeChecker_Cfg.default_univs_to_zero =
                   (uu___2.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                 FStarC_TypeChecker_Cfg.tactics =
                   (uu___2.FStarC_TypeChecker_Cfg.tactics);
                 FStarC_TypeChecker_Cfg.reduce_projections =
                   (uu___2.FStarC_TypeChecker_Cfg.reduce_projections)
               } in
             {
               FStarC_TypeChecker_Cfg.steps = uu___1;
               FStarC_TypeChecker_Cfg.tcenv =
                 (cfg.FStarC_TypeChecker_Cfg.tcenv);
               FStarC_TypeChecker_Cfg.debug =
                 (cfg.FStarC_TypeChecker_Cfg.debug);
               FStarC_TypeChecker_Cfg.delta_level =
                 (cfg.FStarC_TypeChecker_Cfg.delta_level);
               FStarC_TypeChecker_Cfg.primitive_steps =
                 (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
               FStarC_TypeChecker_Cfg.strong =
                 (cfg.FStarC_TypeChecker_Cfg.strong);
               FStarC_TypeChecker_Cfg.memoize_lazy =
                 (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
               FStarC_TypeChecker_Cfg.normalize_pure_lets =
                 (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
               FStarC_TypeChecker_Cfg.reifying =
                 (cfg.FStarC_TypeChecker_Cfg.reifying);
               FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                 (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
             } in
           FStar_Pervasives_Native.Some
             ((FStar_Pervasives_Native.Some cfg'), stack1))
  | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_fully ->
      let cfg' =
        {
          FStarC_TypeChecker_Cfg.steps =
            (let uu___ = cfg.FStarC_TypeChecker_Cfg.steps in
             {
               FStarC_TypeChecker_Cfg.beta =
                 (uu___.FStarC_TypeChecker_Cfg.beta);
               FStarC_TypeChecker_Cfg.iota =
                 (uu___.FStarC_TypeChecker_Cfg.iota);
               FStarC_TypeChecker_Cfg.zeta =
                 (uu___.FStarC_TypeChecker_Cfg.zeta);
               FStarC_TypeChecker_Cfg.zeta_full =
                 (uu___.FStarC_TypeChecker_Cfg.zeta_full);
               FStarC_TypeChecker_Cfg.weak =
                 (uu___.FStarC_TypeChecker_Cfg.weak);
               FStarC_TypeChecker_Cfg.hnf =
                 (uu___.FStarC_TypeChecker_Cfg.hnf);
               FStarC_TypeChecker_Cfg.primops =
                 (uu___.FStarC_TypeChecker_Cfg.primops);
               FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                 (uu___.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
               FStarC_TypeChecker_Cfg.unfold_until =
                 (FStar_Pervasives_Native.Some
                    FStarC_Syntax_Syntax.delta_constant);
               FStarC_TypeChecker_Cfg.unfold_only =
                 FStar_Pervasives_Native.None;
               FStarC_TypeChecker_Cfg.unfold_once =
                 (uu___.FStarC_TypeChecker_Cfg.unfold_once);
               FStarC_TypeChecker_Cfg.unfold_fully =
                 FStar_Pervasives_Native.None;
               FStarC_TypeChecker_Cfg.unfold_attr =
                 FStar_Pervasives_Native.None;
               FStarC_TypeChecker_Cfg.unfold_qual =
                 FStar_Pervasives_Native.None;
               FStarC_TypeChecker_Cfg.unfold_namespace =
                 FStar_Pervasives_Native.None;
               FStarC_TypeChecker_Cfg.dont_unfold_attr =
                 (uu___.FStarC_TypeChecker_Cfg.dont_unfold_attr);
               FStarC_TypeChecker_Cfg.pure_subterms_within_computations =
                 (uu___.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
               FStarC_TypeChecker_Cfg.simplify =
                 (uu___.FStarC_TypeChecker_Cfg.simplify);
               FStarC_TypeChecker_Cfg.erase_universes =
                 (uu___.FStarC_TypeChecker_Cfg.erase_universes);
               FStarC_TypeChecker_Cfg.allow_unbound_universes =
                 (uu___.FStarC_TypeChecker_Cfg.allow_unbound_universes);
               FStarC_TypeChecker_Cfg.reify_ =
                 (uu___.FStarC_TypeChecker_Cfg.reify_);
               FStarC_TypeChecker_Cfg.compress_uvars =
                 (uu___.FStarC_TypeChecker_Cfg.compress_uvars);
               FStarC_TypeChecker_Cfg.no_full_norm =
                 (uu___.FStarC_TypeChecker_Cfg.no_full_norm);
               FStarC_TypeChecker_Cfg.check_no_uvars =
                 (uu___.FStarC_TypeChecker_Cfg.check_no_uvars);
               FStarC_TypeChecker_Cfg.unmeta =
                 (uu___.FStarC_TypeChecker_Cfg.unmeta);
               FStarC_TypeChecker_Cfg.unascribe =
                 (uu___.FStarC_TypeChecker_Cfg.unascribe);
               FStarC_TypeChecker_Cfg.in_full_norm_request =
                 (uu___.FStarC_TypeChecker_Cfg.in_full_norm_request);
               FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                 (uu___.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
               FStarC_TypeChecker_Cfg.nbe_step =
                 (uu___.FStarC_TypeChecker_Cfg.nbe_step);
               FStarC_TypeChecker_Cfg.for_extraction =
                 (uu___.FStarC_TypeChecker_Cfg.for_extraction);
               FStarC_TypeChecker_Cfg.unrefine =
                 (uu___.FStarC_TypeChecker_Cfg.unrefine);
               FStarC_TypeChecker_Cfg.default_univs_to_zero =
                 (uu___.FStarC_TypeChecker_Cfg.default_univs_to_zero);
               FStarC_TypeChecker_Cfg.tactics =
                 (uu___.FStarC_TypeChecker_Cfg.tactics);
               FStarC_TypeChecker_Cfg.reduce_projections =
                 (uu___.FStarC_TypeChecker_Cfg.reduce_projections)
             });
          FStarC_TypeChecker_Cfg.tcenv = (cfg.FStarC_TypeChecker_Cfg.tcenv);
          FStarC_TypeChecker_Cfg.debug = (cfg.FStarC_TypeChecker_Cfg.debug);
          FStarC_TypeChecker_Cfg.delta_level =
            (cfg.FStarC_TypeChecker_Cfg.delta_level);
          FStarC_TypeChecker_Cfg.primitive_steps =
            (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
          FStarC_TypeChecker_Cfg.strong = (cfg.FStarC_TypeChecker_Cfg.strong);
          FStarC_TypeChecker_Cfg.memoize_lazy =
            (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
          FStarC_TypeChecker_Cfg.normalize_pure_lets =
            (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
          FStarC_TypeChecker_Cfg.reifying =
            (cfg.FStarC_TypeChecker_Cfg.reifying);
          FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
            (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
        } in
      FStar_Pervasives_Native.Some
        ((FStar_Pervasives_Native.Some cfg'), stack1)
  | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_reify ->
      let rec push e s =
        match s with
        | [] -> [e]
        | (UnivArgs (us, r))::t -> (UnivArgs (us, r)) :: (push e t)
        | h::t -> e :: h :: t in
      let ref =
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_constant
             (FStarC_Const.Const_reflect (FStarC_Syntax_Syntax.lid_of_fv fv)))
          FStarC_Range_Type.dummyRange in
      let stack2 =
        push
          (App
             (empty_env, ref, FStar_Pervasives_Native.None,
               FStarC_Range_Type.dummyRange)) stack1 in
      FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None, stack2)
let on_domain_lids : FStarC_Ident.lident Prims.list=
  [FStarC_Parser_Const.fext_on_domain_lid;
  FStarC_Parser_Const.fext_on_dom_lid;
  FStarC_Parser_Const.fext_on_domain_g_lid;
  FStarC_Parser_Const.fext_on_dom_g_lid]
let is_fext_on_domain (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let is_on_dom fv =
    FStarC_List.existsb (fun l -> FStarC_Syntax_Syntax.fv_eq_lid fv l)
      on_domain_lids in
  let uu___ = FStarC_Syntax_Util.head_and_args_full t in
  match uu___ with
  | (hd, args) ->
      let uu___1 =
        let uu___2 = FStarC_Syntax_Util.un_uinst hd in
        uu___2.FStarC_Syntax_Syntax.n in
      (match uu___1 with
       | FStarC_Syntax_Syntax.Tm_fvar fv when
           let uu___2 = is_on_dom fv in
           if uu___2
           then (FStarC_List.length args) = (Prims.of_int 3)
           else false ->
           let f =
             FStar_Pervasives_Native.fst
               (FStarC_List.hd (FStarC_List.tl (FStarC_List.tl args))) in
           FStar_Pervasives_Native.Some f
       | uu___2 -> FStar_Pervasives_Native.None)
let __get_n_binders :
  (FStarC_TypeChecker_Env.env ->
     FStarC_TypeChecker_Env.step Prims.list ->
       Prims.int ->
         FStarC_Syntax_Syntax.term ->
           (FStarC_Syntax_Syntax.binder Prims.list *
             FStarC_Syntax_Syntax.comp))
    FStarC_Effect.ref=
  FStarC_Effect.mk_ref
    (fun e s n t ->
       FStarC_Effect.failwith "Impossible: __get_n_binders unset")
let is_partial_primop_app (cfg : FStarC_TypeChecker_Cfg.cfg)
  (t : FStarC_Syntax_Syntax.term) : Prims.bool=
  let uu___ = FStarC_Syntax_Util.head_and_args_full t in
  match uu___ with
  | (hd, args) ->
      let uu___1 =
        let uu___2 = FStarC_Syntax_Util.un_uinst hd in
        uu___2.FStarC_Syntax_Syntax.n in
      (match uu___1 with
       | FStarC_Syntax_Syntax.Tm_fvar fv ->
           let uu___2 = FStarC_TypeChecker_Cfg.find_prim_step cfg fv in
           (match uu___2 with
            | FStar_Pervasives_Native.Some prim_step ->
                prim_step.FStarC_TypeChecker_Primops_Base.arity >
                  (FStarC_List.length args)
            | FStar_Pervasives_Native.None -> false)
       | uu___2 -> false)
let maybe_drop_rc_typ (cfg : FStarC_TypeChecker_Cfg.cfg)
  (rc : FStarC_Syntax_Syntax.residual_comp) :
  FStarC_Syntax_Syntax.residual_comp=
  if (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
  then
    {
      FStarC_Syntax_Syntax.residual_effect =
        (rc.FStarC_Syntax_Syntax.residual_effect);
      FStarC_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.None;
      FStarC_Syntax_Syntax.residual_flags =
        (rc.FStarC_Syntax_Syntax.residual_flags)
    }
  else rc
let get_extraction_mode (env1 : FStarC_TypeChecker_Env.env)
  (m : FStarC_Ident.lident) : FStarC_Syntax_Syntax.eff_extraction_mode=
  let norm_m = FStarC_TypeChecker_Env.norm_eff_name env1 m in
  let uu___ = FStarC_TypeChecker_Env.get_effect_decl env1 norm_m in
  uu___.FStarC_Syntax_Syntax.extraction_mode
let can_reify_for_extraction (env1 : 'uuuuu) (m : FStarC_Ident.lident) :
  Prims.bool= false
let rec args_are_binders :
  'uuuuu .
    (FStarC_Syntax_Syntax.term * 'uuuuu) Prims.list ->
      FStarC_Syntax_Syntax.binder Prims.list -> Prims.bool
  =
  fun args bs ->
    match (args, bs) with
    | ((t, uu___)::args1, b::bs1) ->
        let uu___1 =
          let uu___2 = FStarC_Syntax_Subst.compress t in
          uu___2.FStarC_Syntax_Syntax.n in
        (match uu___1 with
         | FStarC_Syntax_Syntax.Tm_name bv' ->
             if
               FStarC_Syntax_Syntax.bv_eq b.FStarC_Syntax_Syntax.binder_bv
                 bv'
             then args_are_binders args1 bs1
             else false
         | uu___2 -> false)
    | ([], []) -> true
    | (uu___, uu___1) -> false
let is_applied (cfg : FStarC_TypeChecker_Cfg.cfg)
  (bs : FStarC_Syntax_Syntax.binders) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option=
  if (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
  then
    (let uu___1 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
     let uu___2 =
       FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t in
     FStarC_Format.print2 "WPE> is_applied %s -- %s\n" uu___1 uu___2)
  else ();
  (let uu___1 = FStarC_Syntax_Util.head_and_args_full t in
   match uu___1 with
   | (hd, args) ->
       let uu___2 =
         let uu___3 = FStarC_Syntax_Subst.compress hd in
         uu___3.FStarC_Syntax_Syntax.n in
       (match uu___2 with
        | FStarC_Syntax_Syntax.Tm_name bv when args_are_binders args bs ->
            (if (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
             then
               (let uu___4 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
                let uu___5 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv bv in
                let uu___6 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term hd in
                FStarC_Format.print3
                  "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                  uu___4 uu___5 uu___6)
             else ();
             FStar_Pervasives_Native.Some bv)
        | uu___3 -> FStar_Pervasives_Native.None))
let is_quantified_const (uu___2 : FStarC_TypeChecker_Cfg.cfg)
  (uu___1 : FStarC_Syntax_Syntax.bv) (uu___ : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  (fun cfg bv phi ->
     let guard1 b =
       if b
       then FStar_Pervasives_Native.Some ()
       else FStar_Pervasives_Native.None in
     let phi0 = phi in
     let types_match bs =
       let uu___ =
         let uu___1 = FStarC_Effect.op_Bang __get_n_binders in
         uu___1 cfg.FStarC_TypeChecker_Cfg.tcenv
           [FStarC_TypeChecker_Env.AllowUnboundUniverses]
           (FStarC_List.length bs) bv.FStarC_Syntax_Syntax.sort in
       match uu___ with
       | (bs_q, uu___1) ->
           let rec unrefine_true t =
             let uu___2 =
               let uu___3 = FStarC_Syntax_Subst.compress t in
               uu___3.FStarC_Syntax_Syntax.n in
             match uu___2 with
             | FStarC_Syntax_Syntax.Tm_refine
                 { FStarC_Syntax_Syntax.b2 = b;
                   FStarC_Syntax_Syntax.phi = phi1;_}
                 when
                 FStarC_Syntax_Util.term_eq phi1 FStarC_Syntax_Util.t_true ->
                 unrefine_true b.FStarC_Syntax_Syntax.sort
             | uu___3 -> t in
           if (FStarC_List.length bs) = (FStarC_List.length bs_q)
           then
             FStarC_List.forall2
               (fun b1 b2 ->
                  let s1 =
                    unrefine_true
                      (b1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                  let s2 =
                    unrefine_true
                      (b2.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                  FStarC_Syntax_Util.term_eq s1 s2) bs bs_q
           else false in
     let is_bv bv1 t =
       let uu___ =
         let uu___1 = FStarC_Syntax_Subst.compress t in
         uu___1.FStarC_Syntax_Syntax.n in
       match uu___ with
       | FStarC_Syntax_Syntax.Tm_name bv' ->
           FStarC_Syntax_Syntax.bv_eq bv1 bv'
       | uu___1 -> false in
     let replace_full_applications_with bv1 arity s t =
       let chgd = FStarC_Effect.mk_ref false in
       let t' =
         FStarC_Syntax_Visit.visit_term false
           (fun t1 ->
              let uu___ = FStarC_Syntax_Util.head_and_args_full t1 in
              match uu___ with
              | (hd, args) ->
                  let uu___1 =
                    if (FStarC_List.length args) = arity
                    then is_bv bv1 hd
                    else false in
                  if uu___1
                  then (FStarC_Effect.op_Colon_Equals chgd true; s)
                  else t1) t in
       let uu___ = FStarC_Effect.op_Bang chgd in (t', uu___) in
     let uu___ = FStarC_Syntax_Formula.destruct_typ_as_formula phi in
     Obj.magic
       (FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option () ()
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun form ->
                let form = Obj.magic form in
                match form with
                | FStarC_Syntax_Formula.BaseConn
                    (lid, (p, uu___1)::(q, uu___2)::[]) when
                    FStarC_Ident.lid_equals lid FStarC_Parser_Const.imp_lid
                    ->
                    Obj.magic
                      (Obj.repr
                         (if
                            (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                          then
                            (let uu___4 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_term p in
                             let uu___5 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_term q in
                             FStarC_Format.print2 "WPE> p = (%s); q = (%s)\n"
                               uu___4 uu___5)
                          else ();
                          (let uu___4 =
                             let uu___5 =
                               FStarC_Syntax_Formula.destruct_typ_as_formula
                                 p in
                             match uu___5 with
                             | FStar_Pervasives_Native.None ->
                                 Obj.magic
                                   (Obj.repr
                                      (let uu___6 =
                                         let uu___7 =
                                           FStarC_Syntax_Subst.compress p in
                                         uu___7.FStarC_Syntax_Syntax.n in
                                       match uu___6 with
                                       | FStarC_Syntax_Syntax.Tm_bvar bv'
                                           when
                                           FStarC_Syntax_Syntax.bv_eq bv bv'
                                           ->
                                           (if
                                              (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                                            then
                                              FStarC_Format.print_string
                                                "WPE> Case 1\n"
                                            else ();
                                            (let q' =
                                               FStarC_Syntax_Subst.subst
                                                 [FStarC_Syntax_Syntax.NT
                                                    (bv,
                                                      FStarC_Syntax_Util.t_true)]
                                                 q in
                                             FStar_Pervasives_Native.Some q'))
                                       | uu___7 ->
                                           FStar_Pervasives_Native.None))
                             | FStar_Pervasives_Native.Some
                                 (FStarC_Syntax_Formula.BaseConn
                                 (lid1, (p1, uu___6)::[])) when
                                 FStarC_Ident.lid_equals lid1
                                   FStarC_Parser_Const.not_lid
                                 ->
                                 Obj.magic
                                   (Obj.repr
                                      (let uu___7 =
                                         let uu___8 =
                                           FStarC_Syntax_Subst.compress p1 in
                                         uu___8.FStarC_Syntax_Syntax.n in
                                       match uu___7 with
                                       | FStarC_Syntax_Syntax.Tm_bvar bv'
                                           when
                                           FStarC_Syntax_Syntax.bv_eq bv bv'
                                           ->
                                           (if
                                              (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                                            then
                                              FStarC_Format.print_string
                                                "WPE> Case 2\n"
                                            else ();
                                            (let q' =
                                               FStarC_Syntax_Subst.subst
                                                 [FStarC_Syntax_Syntax.NT
                                                    (bv,
                                                      FStarC_Syntax_Util.t_false)]
                                                 q in
                                             FStar_Pervasives_Native.Some q'))
                                       | uu___8 ->
                                           FStar_Pervasives_Native.None))
                             | FStar_Pervasives_Native.Some
                                 (FStarC_Syntax_Formula.QAll
                                 (bs, pats, phi1)) when types_match bs ->
                                 Obj.magic
                                   (Obj.repr
                                      (let uu___6 =
                                         FStarC_Syntax_Formula.destruct_typ_as_formula
                                           phi1 in
                                       match uu___6 with
                                       | FStar_Pervasives_Native.None ->
                                           Obj.repr
                                             (let uu___7 =
                                                is_applied cfg bs phi1 in
                                              FStarC_Class_Monad.op_let_Bang
                                                FStarC_Class_Monad.monad_option
                                                () () (Obj.magic uu___7)
                                                (fun uu___8 ->
                                                   (fun bv' ->
                                                      let bv' = Obj.magic bv' in
                                                      Obj.magic
                                                        (FStarC_Class_Monad.op_let_Bang
                                                           FStarC_Class_Monad.monad_option
                                                           () ()
                                                           (guard1
                                                              (FStarC_Syntax_Syntax.bv_eq
                                                                 bv bv'))
                                                           (fun uu___8 ->
                                                              (fun uu___8 ->
                                                                 let uu___8 =
                                                                   Obj.magic
                                                                    uu___8 in
                                                                 if
                                                                   (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                                                                 then
                                                                   FStarC_Format.print_string
                                                                    "WPE> Case 3\n"
                                                                 else ();
                                                                 (let uu___10
                                                                    =
                                                                    replace_full_applications_with
                                                                    bv
                                                                    (FStarC_List.length
                                                                    bs)
                                                                    FStarC_Syntax_Util.t_true
                                                                    q in
                                                                  match uu___10
                                                                  with
                                                                  | (q',
                                                                    chgd) ->
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    (guard1
                                                                    chgd)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    uu___11 in
                                                                    Obj.magic
                                                                    (FStar_Pervasives_Native.Some
                                                                    q'))
                                                                    uu___11))))
                                                                uu___8)))
                                                     uu___8))
                                       | FStar_Pervasives_Native.Some
                                           (FStarC_Syntax_Formula.BaseConn
                                           (lid1, (p1, uu___7)::[])) when
                                           FStarC_Ident.lid_equals lid1
                                             FStarC_Parser_Const.not_lid
                                           ->
                                           Obj.repr
                                             (let uu___8 =
                                                is_applied cfg bs p1 in
                                              FStarC_Class_Monad.op_let_Bang
                                                FStarC_Class_Monad.monad_option
                                                () () (Obj.magic uu___8)
                                                (fun uu___9 ->
                                                   (fun bv' ->
                                                      let bv' = Obj.magic bv' in
                                                      Obj.magic
                                                        (FStarC_Class_Monad.op_let_Bang
                                                           FStarC_Class_Monad.monad_option
                                                           () ()
                                                           (guard1
                                                              (FStarC_Syntax_Syntax.bv_eq
                                                                 bv bv'))
                                                           (fun uu___9 ->
                                                              (fun uu___9 ->
                                                                 let uu___9 =
                                                                   Obj.magic
                                                                    uu___9 in
                                                                 if
                                                                   (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                                                                 then
                                                                   FStarC_Format.print_string
                                                                    "WPE> Case 4\n"
                                                                 else ();
                                                                 (let uu___11
                                                                    =
                                                                    replace_full_applications_with
                                                                    bv
                                                                    (FStarC_List.length
                                                                    bs)
                                                                    FStarC_Syntax_Util.t_false
                                                                    q in
                                                                  match uu___11
                                                                  with
                                                                  | (q',
                                                                    chgd) ->
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    (guard1
                                                                    chgd)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    uu___12 in
                                                                    Obj.magic
                                                                    (FStar_Pervasives_Native.Some
                                                                    q'))
                                                                    uu___12))))
                                                                uu___9)))
                                                     uu___9))
                                       | uu___7 ->
                                           Obj.repr
                                             FStar_Pervasives_Native.None))
                             | uu___6 ->
                                 Obj.magic
                                   (Obj.repr FStar_Pervasives_Native.None) in
                           FStarC_Class_Monad.op_let_Bang
                             FStarC_Class_Monad.monad_option () ()
                             (Obj.magic uu___4)
                             (fun uu___5 ->
                                (fun q' ->
                                   let q' = Obj.magic q' in
                                   let phi' =
                                     let uu___5 =
                                       FStarC_Syntax_Syntax.fvar
                                         FStarC_Parser_Const.imp_lid
                                         FStar_Pervasives_Native.None in
                                     FStarC_Syntax_Util.mk_app uu___5
                                       [FStarC_Syntax_Syntax.as_arg p;
                                       FStarC_Syntax_Syntax.as_arg q'] in
                                   Obj.magic
                                     (FStar_Pervasives_Native.Some phi'))
                                  uu___5))))
                | uu___1 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None))
               uu___1))) uu___2 uu___1 uu___
let is_forall_const (uu___1 : FStarC_TypeChecker_Cfg.cfg)
  (uu___ : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  (fun cfg phi ->
     let uu___ = FStarC_Syntax_Formula.destruct_typ_as_formula phi in
     match uu___ with
     | FStar_Pervasives_Native.Some (FStarC_Syntax_Formula.QAll
         (b::[], uu___1, phi')) ->
         Obj.magic
           (Obj.repr
              (if
                 (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
               then
                 (let uu___3 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv
                      b.FStarC_Syntax_Syntax.binder_bv in
                  let uu___4 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      phi' in
                  FStarC_Format.print2 "WPE> QAll [%s] %s\n" uu___3 uu___4)
               else ();
               (let uu___3 =
                  is_quantified_const cfg b.FStarC_Syntax_Syntax.binder_bv
                    phi' in
                FStarC_Class_Monad.op_let_Bang
                  FStarC_Class_Monad.monad_option () () (Obj.magic uu___3)
                  (fun uu___4 ->
                     (fun phi'1 ->
                        let phi'1 = Obj.magic phi'1 in
                        let uu___4 =
                          let uu___5 =
                            (cfg.FStarC_TypeChecker_Cfg.tcenv).FStarC_TypeChecker_Env.universe_of
                              cfg.FStarC_TypeChecker_Cfg.tcenv
                              (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                          FStarC_Syntax_Util.mk_forall uu___5
                            b.FStarC_Syntax_Syntax.binder_bv phi'1 in
                        Obj.magic (FStar_Pervasives_Native.Some uu___4))
                       uu___4))))
     | uu___1 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)) uu___1
    uu___
let is_one_point (cfg : 'uuuuu) (phi : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let rec conjuncts t =
    let uu___ = FStarC_Syntax_Util.head_and_args_full t in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (a, uu___2)::(b, uu___3)::[])
             when
             FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.and_lid ->
             let uu___4 = conjuncts a in
             let uu___5 = conjuncts b in FStarC_List.op_At uu___4 uu___5
         | uu___2 -> [t]) in
  let mk_conjs ts =
    FStarC_List.fold_right FStarC_Syntax_Util.mk_conj_simp ts
      FStarC_Syntax_Util.t_true in
  let as_defn x t =
    let is_x t1 =
      let uu___ =
        let uu___1 = FStarC_Syntax_Subst.compress t1 in
        uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_name y -> FStarC_Syntax_Syntax.bv_eq x y
      | uu___1 -> false in
    let uu___ = FStarC_Syntax_Util.head_and_args_full t in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv,
            uu___2::(lhs, uu___3)::(rhs, uu___4)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.eq2_lid ->
             let uu___5 =
               let uu___6 = is_x lhs in
               if uu___6
               then
                 let uu___7 =
                   let uu___8 = FStarC_Syntax_Free.names rhs in
                   FStarC_Class_Setlike.mem
                     (FStarC_FlatSet.setlike_flat_set
                        FStarC_Syntax_Syntax.ord_bv) x uu___8 in
                 Prims.not uu___7
               else false in
             if uu___5
             then FStar_Pervasives_Native.Some rhs
             else
               (let uu___6 =
                  let uu___7 = is_x rhs in
                  if uu___7
                  then
                    let uu___8 =
                      let uu___9 = FStarC_Syntax_Free.names lhs in
                      FStarC_Class_Setlike.mem
                        (FStarC_FlatSet.setlike_flat_set
                           FStarC_Syntax_Syntax.ord_bv) x uu___9 in
                    Prims.not uu___8
                  else false in
                if uu___6
                then FStar_Pervasives_Native.Some lhs
                else FStar_Pervasives_Native.None)
         | uu___2 -> FStar_Pervasives_Native.None) in
  let split x t =
    let cs = conjuncts t in
    let rec go pre cs1 =
      match cs1 with
      | [] -> FStar_Pervasives_Native.None
      | c::cs2 ->
          let uu___ = as_defn x c in
          (match uu___ with
           | FStar_Pervasives_Native.Some v ->
               let uu___1 =
                 let uu___2 =
                   mk_conjs (FStarC_List.op_At (FStarC_List.rev pre) cs2) in
                 (v, uu___2) in
               FStar_Pervasives_Native.Some uu___1
           | FStar_Pervasives_Native.None -> go (c :: pre) cs2) in
    go [] cs in
  let quant =
    let uu___ = FStarC_Syntax_Util.head_and_args_full phi in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (t, uu___2)::[]) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Parser_Const.forall_lid
             then FStar_Pervasives_Native.Some (true, t)
             else
               if
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.exists_lid
               then FStar_Pervasives_Native.Some (false, t)
               else FStar_Pervasives_Native.None
         | (FStarC_Syntax_Syntax.Tm_fvar fv, uu___2::(t, uu___3)::[]) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Parser_Const.forall_lid
             then FStar_Pervasives_Native.Some (true, t)
             else
               if
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.exists_lid
               then FStar_Pervasives_Native.Some (false, t)
               else FStar_Pervasives_Native.None
         | uu___2 -> FStar_Pervasives_Native.None) in
  let typing x v =
    FStarC_Syntax_Util.refinement_hypothesis x.FStarC_Syntax_Syntax.sort v in
  let keep_if_small res =
    let uu___ =
      let uu___1 = FStarC_Syntax_Util.sizeof res in
      let uu___2 =
        let uu___3 = FStarC_Syntax_Util.sizeof phi in
        uu___3 + (Prims.of_int 100) in
      uu___1 > uu___2 in
    if uu___
    then FStar_Pervasives_Native.None
    else FStar_Pervasives_Native.Some res in
  match quant with
  | FStar_Pervasives_Native.Some (is_forall, t) ->
      let uu___ =
        let uu___1 = FStarC_Syntax_Subst.compress t in
        uu___1.FStarC_Syntax_Syntax.n in
      (match uu___ with
       | FStarC_Syntax_Syntax.Tm_abs
           { FStarC_Syntax_Syntax.b = b; FStarC_Syntax_Syntax.body = body;
             FStarC_Syntax_Syntax.rc_opt = uu___1;_}
           ->
           let uu___2 = FStarC_Syntax_Subst.open_term [b] body in
           (match uu___2 with
            | (bs, body1) ->
                let x = (FStarC_List.hd bs).FStarC_Syntax_Syntax.binder_bv in
                let uu___3 =
                  let uu___4 = FStarC_Syntax_Subst.compress body1 in
                  uu___4.FStarC_Syntax_Syntax.n in
                (match uu___3 with
                 | FStarC_Syntax_Syntax.Tm_meta
                     { FStarC_Syntax_Syntax.tm2 = uu___4;
                       FStarC_Syntax_Syntax.meta =
                         FStarC_Syntax_Syntax.Meta_pattern uu___5;_}
                     -> FStar_Pervasives_Native.None
                 | uu___4 ->
                     if is_forall
                     then FStar_Pervasives_Native.None
                     else
                       (let uu___5 = split x body1 in
                        match uu___5 with
                        | FStar_Pervasives_Native.Some (v, rest) ->
                            let uu___6 =
                              let uu___7 =
                                let uu___8 = typing x v in
                                FStarC_Syntax_Util.mk_conj_simp uu___8 rest in
                              FStarC_Syntax_Subst.subst
                                [FStarC_Syntax_Syntax.NT (x, v)] uu___7 in
                            keep_if_small uu___6
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None)))
       | uu___1 -> FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
type norm_request_kind =
  | NormalizeTerm 
  | Normalize 
  | Norm 
let uu___is_NormalizeTerm (projectee : norm_request_kind) : Prims.bool=
  match projectee with | NormalizeTerm -> true | uu___ -> false
let uu___is_Normalize (projectee : norm_request_kind) : Prims.bool=
  match projectee with | Normalize -> true | uu___ -> false
let uu___is_Norm (projectee : norm_request_kind) : Prims.bool=
  match projectee with | Norm -> true | uu___ -> false
let is_norm_request_head (fv : FStarC_Syntax_Syntax.fv) :
  norm_request_kind FStar_Pervasives_Native.option=
  if FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.normalize_term
  then FStar_Pervasives_Native.Some NormalizeTerm
  else
    if FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.normalize
    then FStar_Pervasives_Native.Some Normalize
    else
      if FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.norm
      then FStar_Pervasives_Native.Some Norm
      else FStar_Pervasives_Native.None
let rec norm (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env) (stack1 : stack)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let rec collapse_metas st =
    match st with
    | (Meta (uu___, FStarC_Syntax_Syntax.Meta_monadic uu___1, uu___2))::(Meta
        (e, FStarC_Syntax_Syntax.Meta_monadic m, r))::st' ->
        collapse_metas ((Meta (e, (FStarC_Syntax_Syntax.Meta_monadic m), r))
          :: st')
    | uu___ -> st in
  let stack2 = collapse_metas stack1 in
  let t1 =
    if (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.norm_delayed
    then
      (match t.FStarC_Syntax_Syntax.n with
       | FStarC_Syntax_Syntax.Tm_delayed uu___1 ->
           let uu___2 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
           FStarC_Format.print1 "NORM delayed: %s\n" uu___2
       | uu___1 -> ())
    else ();
    FStarC_Syntax_Subst.compress t in
  FStarC_TypeChecker_Cfg.log cfg
    (fun uu___1 ->
       let uu___2 =
         FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
       let uu___3 =
         FStarC_Class_Show.show FStarC_Class_Show.showable_bool
           (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.no_full_norm in
       let uu___4 =
         FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
       let uu___5 =
         FStarC_Class_Show.show FStarC_Class_Show.showable_nat
           (FStarC_List.length env1) in
       let uu___6 =
         FStarC_Class_Show.show
           (FStarC_Class_Show.show_list showable_stack_elt)
           (FStar_Pervasives_Native.fst (firstn (Prims.of_int 4) stack2)) in
       FStarC_Format.print5
         ">>> %s (no_full_norm=%s)\nNorm %s with %s env elements; top of the stack = %s\n"
         uu___2 uu___3 uu___4 uu___5 uu___6);
  FStarC_TypeChecker_Cfg.log_cfg cfg
    (fun uu___2 ->
       let uu___3 =
         FStarC_Class_Show.show FStarC_TypeChecker_Cfg.showable_cfg cfg in
       FStarC_Format.print1 ">>> cfg = %s\n" uu___3);
  (match t1.FStarC_Syntax_Syntax.n with
   | FStarC_Syntax_Syntax.Tm_unknown -> rebuild cfg empty_env stack2 t1
   | FStarC_Syntax_Syntax.Tm_constant uu___2 ->
       rebuild cfg empty_env stack2 t1
   | FStarC_Syntax_Syntax.Tm_name uu___2 -> rebuild cfg empty_env stack2 t1
   | FStarC_Syntax_Syntax.Tm_lazy uu___2 -> rebuild cfg empty_env stack2 t1
   | FStarC_Syntax_Syntax.Tm_fvar
       { FStarC_Syntax_Syntax.fv_name = uu___2;
         FStarC_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
           (FStarC_Syntax_Syntax.Data_ctor);_}
       ->
       (FStarC_TypeChecker_Cfg.log_unfolding cfg
          (fun uu___4 ->
             let uu___5 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
             FStarC_Format.print1 " >> This is a constructor: %s\n" uu___5);
        rebuild cfg empty_env stack2 t1)
   | FStarC_Syntax_Syntax.Tm_fvar
       { FStarC_Syntax_Syntax.fv_name = uu___2;
         FStarC_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
           (FStarC_Syntax_Syntax.Record_ctor uu___3);_}
       ->
       (FStarC_TypeChecker_Cfg.log_unfolding cfg
          (fun uu___5 ->
             let uu___6 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
             FStarC_Format.print1 " >> This is a constructor: %s\n" uu___6);
        rebuild cfg empty_env stack2 t1)
   | FStarC_Syntax_Syntax.Tm_fvar fv when
       if should_consider_norm_requests cfg
       then
         let uu___2 = is_norm_request_head fv in
         match uu___2 with
         | FStar_Pervasives_Native.Some v -> true
         | uu___3 -> false
       else false ->
       let uu___2 =
         let uu___3 = is_norm_request_head fv in
         match uu___3 with | FStar_Pervasives_Native.Some v -> v in
       handle_norm_request cfg env1 stack2 uu___2 t1
   | FStarC_Syntax_Syntax.Tm_fvar fv ->
       let lid = FStarC_Syntax_Syntax.lid_of_fv fv in
       let qninfo =
         FStarC_TypeChecker_Env.lookup_qname cfg.FStarC_TypeChecker_Cfg.tcenv
           lid in
       let uu___2 =
         FStarC_TypeChecker_Env.delta_depth_of_qninfo
           cfg.FStarC_TypeChecker_Cfg.tcenv fv qninfo in
       (match uu___2 with
        | FStarC_Syntax_Syntax.Delta_constant_at_level uu___3 when
            uu___3 = Prims.int_zero ->
            (FStarC_TypeChecker_Cfg.log_unfolding cfg
               (fun uu___5 ->
                  let uu___6 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      t1 in
                  FStarC_Format.print1 " >> This is a constant: %s\n" uu___6);
             rebuild cfg empty_env stack2 t1)
        | uu___3 ->
            let uu___4 = decide_unfolding cfg stack2 fv qninfo in
            (match uu___4 with
             | FStar_Pervasives_Native.Some
                 (FStar_Pervasives_Native.None, stack3) ->
                 do_unfold_fv cfg stack3 t1 qninfo fv
             | FStar_Pervasives_Native.Some
                 (FStar_Pervasives_Native.Some cfg1, stack3) ->
                 do_unfold_fv cfg1 stack3 t1 qninfo fv
             | FStar_Pervasives_Native.None ->
                 rebuild cfg empty_env stack2 t1))
   | FStarC_Syntax_Syntax.Tm_quoted (qt, qi) ->
       let qi1 = FStarC_Syntax_Syntax.on_antiquoted (norm cfg env1 []) qi in
       let t2 =
         FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_quoted (qt, qi1))
           t1.FStarC_Syntax_Syntax.pos in
       let uu___2 = closure_as_term cfg env1 t2 in
       rebuild cfg env1 stack2 uu___2
   | FStarC_Syntax_Syntax.Tm_type u ->
       let u1 = norm_universe cfg env1 u in
       let uu___2 =
         FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_type u1)
           t1.FStarC_Syntax_Syntax.pos in
       rebuild cfg env1 stack2 uu___2
   | FStarC_Syntax_Syntax.Tm_uinst (t', us) ->
       if
         (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.erase_universes
       then norm cfg env1 stack2 t'
       else
         (let us1 =
            let uu___2 =
              let uu___3 = FStarC_List.map (norm_universe cfg env1) us in
              (uu___3, (t1.FStarC_Syntax_Syntax.pos)) in
            UnivArgs uu___2 in
          let stack3 = us1 :: stack2 in norm cfg env1 stack3 t')
   | FStarC_Syntax_Syntax.Tm_bvar x ->
       let uu___2 = lookup_bvar env1 x in
       (match uu___2 with
        | Univ uu___3 ->
            FStarC_Effect.failwith
              "Impossible: term variable is bound to a universe"
        | Dummy -> FStarC_Effect.failwith "Term variable not found"
        | Clos (env2, t0, r, fix) ->
            if
              ((Prims.not fix) ||
                 (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta)
                ||
                (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta_full
            then
              let uu___3 = read_memo cfg r in
              (match uu___3 with
               | FStar_Pervasives_Native.Some (env3, t') ->
                   (FStarC_TypeChecker_Cfg.log cfg
                      (fun uu___5 ->
                         let uu___6 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term t1 in
                         let uu___7 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term t' in
                         FStarC_Format.print2 "Lazy hit: %s cached to %s\n"
                           uu___6 uu___7);
                    (let uu___5 = maybe_weakly_reduced t' in
                     if uu___5
                     then
                       match stack2 with
                       | [] when
                           (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
                             ||
                             (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.compress_uvars
                           -> rebuild cfg env3 stack2 t'
                       | uu___6 -> norm cfg env3 stack2 t'
                     else rebuild cfg env3 stack2 t'))
               | FStar_Pervasives_Native.None ->
                   norm cfg env2 ((MemoLazy r) :: stack2) t0)
            else norm cfg env2 stack2 t0)
   | FStarC_Syntax_Syntax.Tm_abs
       { FStarC_Syntax_Syntax.b = b; FStarC_Syntax_Syntax.body = body;
         FStarC_Syntax_Syntax.rc_opt = rc_opt;_}
       ->
       let rec maybe_strip_meta_divs stack3 =
         match stack3 with
         | [] -> FStar_Pervasives_Native.None
         | (Meta
             (uu___2, FStarC_Syntax_Syntax.Meta_monadic (m, uu___3), uu___4))::tl
             when
             FStarC_Ident.lid_equals m FStarC_Parser_Const.effect_DIV_lid ->
             maybe_strip_meta_divs tl
         | (Meta
             (uu___2, FStarC_Syntax_Syntax.Meta_monadic_lift
              (src, tgt, uu___3), uu___4))::tl
             when
             (FStarC_Ident.lid_equals src FStarC_Parser_Const.effect_PURE_lid)
               &&
               (FStarC_Ident.lid_equals tgt
                  FStarC_Parser_Const.effect_DIV_lid)
             -> maybe_strip_meta_divs tl
         | (Arg uu___2)::uu___3 -> FStar_Pervasives_Native.Some stack3
         | uu___2 -> FStar_Pervasives_Native.None in
       let fallback uu___2 =
         if (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
         then
           let t2 = closure_as_term cfg env1 t1 in rebuild cfg env1 stack2 t2
         else
           (let uu___3 = FStarC_Syntax_Subst.open_term' [b] body in
            match uu___3 with
            | (bs, body1, opening) ->
                let env' =
                  FStarC_List.fold_left
                    (fun env2 uu___4 ->
                       let uu___5 = dummy () in uu___5 :: env2) env1 bs in
                let rc_opt1 =
                  Obj.magic
                    (FStarC_Class_Monad.op_let_Bang
                       FStarC_Class_Monad.monad_option () ()
                       (Obj.magic rc_opt)
                       (fun uu___4 ->
                          (fun rc ->
                             let rc = Obj.magic rc in
                             let rc1 = maybe_drop_rc_typ cfg rc in
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Option.map
                                   (FStarC_Syntax_Subst.subst opening)
                                   rc1.FStarC_Syntax_Syntax.residual_typ in
                               {
                                 FStarC_Syntax_Syntax.residual_effect =
                                   (rc1.FStarC_Syntax_Syntax.residual_effect);
                                 FStarC_Syntax_Syntax.residual_typ = uu___5;
                                 FStarC_Syntax_Syntax.residual_flags =
                                   (rc1.FStarC_Syntax_Syntax.residual_flags)
                               } in
                             Obj.magic (FStar_Pervasives_Native.Some uu___4))
                            uu___4)) in
                (FStarC_TypeChecker_Cfg.log cfg
                   (fun uu___5 ->
                      let uu___6 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                          (FStarC_List.length bs) in
                      FStarC_Format.print1 "\tShifted %s dummies\n" uu___6);
                 (let cfg' =
                    {
                      FStarC_TypeChecker_Cfg.steps =
                        (cfg.FStarC_TypeChecker_Cfg.steps);
                      FStarC_TypeChecker_Cfg.tcenv =
                        (cfg.FStarC_TypeChecker_Cfg.tcenv);
                      FStarC_TypeChecker_Cfg.debug =
                        (cfg.FStarC_TypeChecker_Cfg.debug);
                      FStarC_TypeChecker_Cfg.delta_level =
                        (cfg.FStarC_TypeChecker_Cfg.delta_level);
                      FStarC_TypeChecker_Cfg.primitive_steps =
                        (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
                      FStarC_TypeChecker_Cfg.strong = true;
                      FStarC_TypeChecker_Cfg.memoize_lazy =
                        (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
                      FStarC_TypeChecker_Cfg.normalize_pure_lets =
                        (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
                      FStarC_TypeChecker_Cfg.reifying =
                        (cfg.FStarC_TypeChecker_Cfg.reifying);
                      FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                        (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                    } in
                  let body_norm =
                    norm cfg env'
                      [Abs
                         (env1, bs, env', rc_opt1,
                           (t1.FStarC_Syntax_Syntax.pos))] body1 in
                  rebuild cfg env1 stack2 body_norm))) in
       (match stack2 with
        | (UnivArgs uu___2)::uu___3 ->
            FStarC_Effect.failwith
              "Ill-typed term: universes cannot be applied to term abstraction"
        | (Arg (Univ u, uu___2, uu___3))::stack_rest ->
            let uu___4 =
              let uu___5 =
                let uu___6 = fresh_memo () in
                (FStar_Pervasives_Native.None, (Univ u), uu___6) in
              uu___5 :: env1 in
            norm cfg uu___4 stack_rest t1
        | (Arg (c, uu___2, uu___3))::stack_rest ->
            (FStarC_TypeChecker_Cfg.log cfg
               (fun uu___5 ->
                  let uu___6 = FStarC_Class_Show.show showable_closure c in
                  FStarC_Format.print1 "\tShifted %s\n" uu___6);
             (let uu___5 =
                let uu___6 =
                  let uu___7 = fresh_memo () in
                  ((FStar_Pervasives_Native.Some b), c, uu___7) in
                uu___6 :: env1 in
              norm cfg uu___5 stack_rest body))
        | (MemoLazy r)::stack3 ->
            (set_memo cfg r (env1, t1);
             FStarC_TypeChecker_Cfg.log cfg
               (fun uu___4 ->
                  let uu___5 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      t1 in
                  FStarC_Format.print1 "\tSet memo %s\n" uu___5);
             norm cfg env1 stack3 t1)
        | (Meta uu___2)::uu___3 ->
            (match maybe_strip_meta_divs stack2 with
             | FStar_Pervasives_Native.None -> fallback ()
             | FStar_Pervasives_Native.Some stack3 -> norm cfg env1 stack3 t1)
        | (Match uu___2)::uu___3 -> fallback ()
        | (Let uu___2)::uu___3 -> fallback ()
        | (App uu___2)::uu___3 -> fallback ()
        | (CBVApp uu___2)::uu___3 -> fallback ()
        | (Abs uu___2)::uu___3 -> fallback ()
        | [] -> fallback ())
   | FStarC_Syntax_Syntax.Tm_app uu___2 ->
       let uu___3 = FStarC_Syntax_Util.head_and_args_full t1 in
       (match uu___3 with
        | (head, args) ->
            let push_args_env args1 stack3 =
              FStarC_List.fold_right
                (fun uu___4 stack4 ->
                   match uu___4 with
                   | ((a, aq), env2) ->
                       let a1 =
                         let uu___5 =
                           if
                             ((FStarC_TypeChecker_Cfg.cfg_env cfg).FStarC_TypeChecker_Env.erase_erasable_args
                                ||
                                (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction)
                               ||
                               (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.erase_erasable_args
                           then FStarC_Syntax_Util.aqual_is_erasable aq
                           else false in
                         if uu___5 then FStarC_Syntax_Util.exp_unit else a in
                       let env3 =
                         let uu___5 =
                           let uu___6 = FStarC_Syntax_Subst.compress a1 in
                           uu___6.FStarC_Syntax_Syntax.n in
                         match uu___5 with
                         | FStarC_Syntax_Syntax.Tm_name uu___6 -> empty_env
                         | FStarC_Syntax_Syntax.Tm_constant uu___6 ->
                             empty_env
                         | FStarC_Syntax_Syntax.Tm_lazy uu___6 -> empty_env
                         | FStarC_Syntax_Syntax.Tm_fvar uu___6 -> empty_env
                         | uu___6 -> env2 in
                       let uu___5 =
                         let uu___6 =
                           let uu___7 =
                             let uu___8 =
                               let uu___9 = fresh_cfg_memo () in
                               (env3, a1, uu___9, false) in
                             Clos uu___8 in
                           (uu___7, aq, (t1.FStarC_Syntax_Syntax.pos)) in
                         Arg uu___6 in
                       uu___5 :: stack4) args1 stack3 in
            let push_args env2 args1 stack3 =
              let uu___4 = FStarC_List.map (fun a -> (a, env2)) args1 in
              push_args_env uu___4 stack3 in
            let fallback args1 =
              let stack3 = push_args_env args1 stack2 in
              FStarC_TypeChecker_Cfg.log cfg
                (fun uu___5 ->
                   let uu___6 =
                     FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                       (FStarC_List.length args1) in
                   FStarC_Format.print1 "\tPushed %s arguments\n" uu___6);
              norm cfg env1 stack3 head in
            let unfold_fallback args1 =
              let uu___4 = unfold_disc_proj_for_extraction cfg head in
              match uu___4 with
              | FStar_Pervasives_Native.None -> fallback args1
              | FStar_Pervasives_Native.Some (us_names, def) ->
                  let us =
                    let uu___5 =
                      let uu___6 = FStarC_Syntax_Subst.compress head in
                      uu___6.FStarC_Syntax_Syntax.n in
                    match uu___5 with
                    | FStarC_Syntax_Syntax.Tm_uinst (uu___6, us1) ->
                        FStarC_List.map (norm_universe cfg env1) us1
                    | uu___6 -> [] in
                  let us1 =
                    if
                      (FStarC_List.length us) = (FStarC_List.length us_names)
                    then FStar_Pervasives_Native.Some us
                    else
                      if
                        (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.erase_universes
                          ||
                          (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.allow_unbound_universes
                      then
                        (let uu___5 =
                           FStarC_List.map
                             (fun uu___6 -> FStarC_Syntax_Syntax.U_unknown)
                             us_names in
                         FStar_Pervasives_Native.Some uu___5)
                      else FStar_Pervasives_Native.None in
                  (match us1 with
                   | FStar_Pervasives_Native.None -> fallback args1
                   | FStar_Pervasives_Native.Some us2 ->
                       let def1 =
                         let uu___5 =
                           FStarC_TypeChecker_Env.inst_tscheme_with
                             (us_names, def) us2 in
                         FStar_Pervasives_Native.snd uu___5 in
                       let stack3 = push_args_env args1 stack2 in
                       norm cfg empty_env stack3 def1) in
            let uu___4 = disc_proj_head cfg head in
            (match uu___4 with
             | FStar_Pervasives_Native.Some (d, is_disc, n_indexed, idx) when
                 (FStarC_List.length args) > n_indexed ->
                 let uu___5 = FStarC_List.nth args n_indexed in
                 (match uu___5 with
                  | (scrutinee0, aq) ->
                      let cfg' = whnf_cfg cfg in
                      let scrutinee = norm cfg' env1 [] scrutinee0 in
                      let uu___6 =
                        reduce_disc_proj cfg d is_disc idx scrutinee in
                      (match uu___6 with
                       | FStar_Pervasives_Native.None ->
                           let args1 =
                             FStarC_List.mapi
                               (fun i a ->
                                  if i = n_indexed
                                  then ((scrutinee, aq), empty_env)
                                  else (a, env1)) args in
                           unfold_fallback args1
                       | FStar_Pervasives_Native.Some field ->
                           (FStarC_TypeChecker_Cfg.log cfg
                              (fun uu___8 ->
                                 let uu___9 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_term t1 in
                                 let uu___10 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_term field in
                                 FStarC_Format.print2
                                   "Reduced projector/discriminator %s to %s\n"
                                   uu___9 uu___10);
                            (let uu___8 =
                               FStarC_Util.first_N
                                 (n_indexed + Prims.int_one) args in
                             match uu___8 with
                             | (uu___9, rest) ->
                                 let stack3 = push_args env1 rest stack2 in
                                 norm cfg empty_env stack3 field))))
             | uu___5 ->
                 let uu___6 = FStarC_List.map (fun a -> (a, env1)) args in
                 fallback uu___6))
   | FStarC_Syntax_Syntax.Tm_refine
       { FStarC_Syntax_Syntax.b2 = x; FStarC_Syntax_Syntax.phi = uu___2;_}
       when
       (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
         ||
         (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unrefine
       -> norm cfg env1 stack2 x.FStarC_Syntax_Syntax.sort
   | FStarC_Syntax_Syntax.Tm_refine
       { FStarC_Syntax_Syntax.b2 = x; FStarC_Syntax_Syntax.phi = f;_} ->
       if (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
       then
         (match (env1, stack2) with
          | ([], []) ->
              let t_x = norm cfg env1 [] x.FStarC_Syntax_Syntax.sort in
              let t2 =
                FStarC_Syntax_Syntax.mk
                  (FStarC_Syntax_Syntax.Tm_refine
                     {
                       FStarC_Syntax_Syntax.b2 =
                         {
                           FStarC_Syntax_Syntax.ppname =
                             (x.FStarC_Syntax_Syntax.ppname);
                           FStarC_Syntax_Syntax.index =
                             (x.FStarC_Syntax_Syntax.index);
                           FStarC_Syntax_Syntax.sort = t_x
                         };
                       FStarC_Syntax_Syntax.phi = f
                     }) t1.FStarC_Syntax_Syntax.pos in
              rebuild cfg env1 stack2 t2
          | uu___2 ->
              let uu___3 = closure_as_term cfg env1 t1 in
              rebuild cfg env1 stack2 uu___3)
       else
         (let t_x = norm cfg env1 [] x.FStarC_Syntax_Syntax.sort in
          let uu___2 =
            FStarC_Syntax_Subst.open_term [FStarC_Syntax_Syntax.mk_binder x]
              f in
          match uu___2 with
          | (closing, f1) ->
              let f2 =
                let uu___3 = let uu___4 = dummy () in uu___4 :: env1 in
                norm cfg uu___3 [] f1 in
              let t2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 = FStarC_Syntax_Subst.close closing f2 in
                    {
                      FStarC_Syntax_Syntax.b2 =
                        {
                          FStarC_Syntax_Syntax.ppname =
                            (x.FStarC_Syntax_Syntax.ppname);
                          FStarC_Syntax_Syntax.index =
                            (x.FStarC_Syntax_Syntax.index);
                          FStarC_Syntax_Syntax.sort = t_x
                        };
                      FStarC_Syntax_Syntax.phi = uu___5
                    } in
                  FStarC_Syntax_Syntax.Tm_refine uu___4 in
                FStarC_Syntax_Syntax.mk uu___3 t1.FStarC_Syntax_Syntax.pos in
              rebuild cfg env1 stack2 t2)
   | FStarC_Syntax_Syntax.Tm_arrow uu___2 ->
       if (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
       then
         let uu___3 = closure_as_term cfg env1 t1 in
         rebuild cfg env1 stack2 uu___3
       else
         (let uu___3 = FStarC_Syntax_Util.arrow_formals_comp_ln_strict t1 in
          match uu___3 with
          | (bs, c) ->
              let uu___4 = FStarC_Syntax_Subst.open_comp bs c in
              (match uu___4 with
               | (bs1, c1) ->
                   let c2 =
                     let uu___5 =
                       FStarC_List.fold_left
                         (fun env2 uu___6 ->
                            let uu___7 = dummy () in uu___7 :: env2) env1 bs1 in
                     norm_comp cfg uu___5 c1 in
                   let close_binders env2 bs2 =
                     let uu___5 = env_subst env2 in
                     FStarC_Syntax_Subst.subst_binders uu___5 bs2 in
                   let bs2 =
                     if
                       (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.hnf
                     then close_binders env1 bs1
                     else norm_binders cfg env1 bs1 in
                   let t2 = FStarC_Syntax_Util.arrow bs2 c2 in
                   rebuild cfg env1 stack2 t2))
   | FStarC_Syntax_Syntax.Tm_ascribed
       { FStarC_Syntax_Syntax.tm = t11; FStarC_Syntax_Syntax.asc = uu___2;
         FStarC_Syntax_Syntax.eff_opt = l;_}
       when
       (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unascribe ->
       norm cfg env1 stack2 t11
   | FStarC_Syntax_Syntax.Tm_ascribed
       { FStarC_Syntax_Syntax.tm = t11; FStarC_Syntax_Syntax.asc = asc;
         FStarC_Syntax_Syntax.eff_opt = l;_}
       ->
       let rec stack_may_reduce s =
         match s with
         | (Match uu___2)::uu___3 when
             (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.beta
             -> true
         | (Arg uu___2)::uu___3 when
             (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.beta
             -> true
         | (App
             (uu___2,
              {
                FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                  (FStarC_Const.Const_reify uu___3);
                FStarC_Syntax_Syntax.pos = uu___4;
                FStarC_Syntax_Syntax.hash_code = uu___5;_},
              uu___6, uu___7))::uu___8
             when
             (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.beta
             -> true
         | (MemoLazy uu___2)::uu___3 when
             (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.beta
             -> true
         | uu___2 -> false in
       if stack_may_reduce stack2
       then
         (FStarC_TypeChecker_Cfg.log cfg
            (fun uu___3 ->
               FStarC_Format.print_string "+++ Dropping ascription \n");
          norm cfg env1 stack2 t11)
       else
         (FStarC_TypeChecker_Cfg.log cfg
            (fun uu___3 ->
               FStarC_Format.print_string "+++ Keeping ascription \n");
          (let t12 = norm cfg env1 [] t11 in
           FStarC_TypeChecker_Cfg.log cfg
             (fun uu___4 ->
                FStarC_Format.print_string "+++ Normalizing ascription \n");
           (let asc1 = norm_ascription cfg env1 asc in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 = FStarC_Syntax_Util.unascribe t12 in
                  {
                    FStarC_Syntax_Syntax.tm = uu___7;
                    FStarC_Syntax_Syntax.asc = asc1;
                    FStarC_Syntax_Syntax.eff_opt = l
                  } in
                FStarC_Syntax_Syntax.Tm_ascribed uu___6 in
              FStarC_Syntax_Syntax.mk uu___5 t1.FStarC_Syntax_Syntax.pos in
            rebuild cfg env1 stack2 uu___4)))
   | FStarC_Syntax_Syntax.Tm_match
       { FStarC_Syntax_Syntax.scrutinee = head;
         FStarC_Syntax_Syntax.ret_opt = asc_opt;
         FStarC_Syntax_Syntax.brs = branches1;
         FStarC_Syntax_Syntax.rc_opt1 = lopt;_}
       ->
       let lopt1 = FStarC_Option.map (maybe_drop_rc_typ cfg) lopt in
       let stack3 =
         (Match
            (env1, asc_opt, branches1, lopt1, cfg,
              (t1.FStarC_Syntax_Syntax.pos)))
         :: stack2 in
       if
         ((cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.iota &&
            (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee)
           &&
           (Prims.not
              (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak)
       then
         let cfg' = weak_cfg cfg in
         let head_norm = norm cfg' env1 [] head in
         rebuild cfg env1 stack3 head_norm
       else norm cfg env1 stack3 head
   | FStarC_Syntax_Syntax.Tm_let
       { FStarC_Syntax_Syntax.lbs = (b, lbs);
         FStarC_Syntax_Syntax.body1 = lbody;_}
       when
       (FStarC_Syntax_Syntax.is_top_level lbs) &&
         (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.compress_uvars
       ->
       let lbs1 =
         FStarC_List.map
           (fun lb ->
              let uu___2 =
                FStarC_Syntax_Subst.univ_var_opening
                  lb.FStarC_Syntax_Syntax.lbunivs in
              match uu___2 with
              | (openings, lbunivs) ->
                  let cfg1 =
                    let uu___3 =
                      FStarC_TypeChecker_Env.push_univ_vars
                        cfg.FStarC_TypeChecker_Cfg.tcenv lbunivs in
                    {
                      FStarC_TypeChecker_Cfg.steps =
                        (cfg.FStarC_TypeChecker_Cfg.steps);
                      FStarC_TypeChecker_Cfg.tcenv = uu___3;
                      FStarC_TypeChecker_Cfg.debug =
                        (cfg.FStarC_TypeChecker_Cfg.debug);
                      FStarC_TypeChecker_Cfg.delta_level =
                        (cfg.FStarC_TypeChecker_Cfg.delta_level);
                      FStarC_TypeChecker_Cfg.primitive_steps =
                        (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
                      FStarC_TypeChecker_Cfg.strong =
                        (cfg.FStarC_TypeChecker_Cfg.strong);
                      FStarC_TypeChecker_Cfg.memoize_lazy =
                        (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
                      FStarC_TypeChecker_Cfg.normalize_pure_lets =
                        (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
                      FStarC_TypeChecker_Cfg.reifying =
                        (cfg.FStarC_TypeChecker_Cfg.reifying);
                      FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                        (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                    } in
                  let norm1 t2 =
                    let uu___3 =
                      let uu___4 = FStarC_Syntax_Subst.subst openings t2 in
                      norm cfg1 env1 [] uu___4 in
                    FStarC_Syntax_Subst.close_univ_vars lbunivs uu___3 in
                  let lbtyp = norm1 lb.FStarC_Syntax_Syntax.lbtyp in
                  let lbdef = norm1 lb.FStarC_Syntax_Syntax.lbdef in
                  {
                    FStarC_Syntax_Syntax.lbname =
                      (lb.FStarC_Syntax_Syntax.lbname);
                    FStarC_Syntax_Syntax.lbunivs = lbunivs;
                    FStarC_Syntax_Syntax.lbtyp = lbtyp;
                    FStarC_Syntax_Syntax.lbeff =
                      (lb.FStarC_Syntax_Syntax.lbeff);
                    FStarC_Syntax_Syntax.lbdef = lbdef;
                    FStarC_Syntax_Syntax.lbattrs =
                      (lb.FStarC_Syntax_Syntax.lbattrs);
                    FStarC_Syntax_Syntax.lbpos =
                      (lb.FStarC_Syntax_Syntax.lbpos)
                  }) lbs in
       let uu___2 =
         FStarC_Syntax_Syntax.mk
           (FStarC_Syntax_Syntax.Tm_let
              {
                FStarC_Syntax_Syntax.lbs = (b, lbs1);
                FStarC_Syntax_Syntax.body1 = lbody
              }) t1.FStarC_Syntax_Syntax.pos in
       rebuild cfg env1 stack2 uu___2
   | FStarC_Syntax_Syntax.Tm_let
       {
         FStarC_Syntax_Syntax.lbs =
           (uu___2,
            { FStarC_Syntax_Syntax.lbname = FStar_Pervasives.Inr uu___3;
              FStarC_Syntax_Syntax.lbunivs = uu___4;
              FStarC_Syntax_Syntax.lbtyp = uu___5;
              FStarC_Syntax_Syntax.lbeff = uu___6;
              FStarC_Syntax_Syntax.lbdef = uu___7;
              FStarC_Syntax_Syntax.lbattrs = uu___8;
              FStarC_Syntax_Syntax.lbpos = uu___9;_}::uu___10);
         FStarC_Syntax_Syntax.body1 = uu___11;_}
       -> rebuild cfg env1 stack2 t1
   | FStarC_Syntax_Syntax.Tm_let
       { FStarC_Syntax_Syntax.lbs = (false, lb::[]);
         FStarC_Syntax_Syntax.body1 = body;_}
       ->
       let uu___2 = FStarC_TypeChecker_Cfg.should_reduce_local_let cfg lb in
       if uu___2
       then
         let binder =
           FStarC_Syntax_Syntax.mk_binder
             (match lb.FStarC_Syntax_Syntax.lbname with
              | FStar_Pervasives.Inl v -> v) in
         let def =
           FStarC_Syntax_Util.unmeta_lift lb.FStarC_Syntax_Syntax.lbdef in
         let env2 =
           let uu___3 =
             let uu___4 =
               let uu___5 =
                 let uu___6 = fresh_cfg_memo () in (env1, def, uu___6, false) in
               Clos uu___5 in
             let uu___5 = fresh_memo () in
             ((FStar_Pervasives_Native.Some binder), uu___4, uu___5) in
           uu___3 :: env1 in
         (FStarC_TypeChecker_Cfg.log cfg
            (fun uu___4 -> FStarC_Format.print_string "+++ Reducing Tm_let\n");
          norm cfg env2 stack2 body)
       else
         (let uu___3 =
            if
              (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.tactics
            then
              let uu___4 =
                FStarC_TypeChecker_Env.norm_eff_name
                  cfg.FStarC_TypeChecker_Cfg.tcenv
                  lb.FStarC_Syntax_Syntax.lbeff in
              FStarC_Syntax_Util.is_div_effect uu___4
            else false in
          if uu___3
          then
            let ffun =
              FStarC_Syntax_Syntax.mk_Tm_abs
                [FStarC_Syntax_Syntax.mk_binder
                   (match lb.FStarC_Syntax_Syntax.lbname with
                    | FStar_Pervasives.Inl v -> v)] body
                FStar_Pervasives_Native.None t1.FStarC_Syntax_Syntax.pos in
            let stack3 =
              (CBVApp
                 (env1, ffun, FStar_Pervasives_Native.None,
                   (t1.FStarC_Syntax_Syntax.pos)))
              :: stack2 in
            (FStarC_TypeChecker_Cfg.log cfg
               (fun uu___5 ->
                  FStarC_Format.print_string "+++ Evaluating DIV Tm_let\n");
             norm cfg env1 stack3 lb.FStarC_Syntax_Syntax.lbdef)
          else
            if (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
            then
              (FStarC_TypeChecker_Cfg.log cfg
                 (fun uu___5 ->
                    FStarC_Format.print_string "+++ Not touching Tm_let\n");
               (let uu___5 = closure_as_term cfg env1 t1 in
                rebuild cfg env1 stack2 uu___5))
            else
              (let uu___4 =
                 FStarC_Syntax_Subst.open_term
                   [FStarC_Syntax_Syntax.mk_binder
                      (match lb.FStarC_Syntax_Syntax.lbname with
                       | FStar_Pervasives.Inl v -> v)] body in
               match uu___4 with
               | (bs, body1) ->
                   (FStarC_TypeChecker_Cfg.log cfg
                      (fun uu___6 ->
                         FStarC_Format.print_string
                           "+++ Normalizing Tm_let -- type");
                    (let ty = norm cfg env1 [] lb.FStarC_Syntax_Syntax.lbtyp in
                     let lbname =
                       let x =
                         (FStarC_List.hd bs).FStarC_Syntax_Syntax.binder_bv in
                       FStar_Pervasives.Inl
                         {
                           FStarC_Syntax_Syntax.ppname =
                             (x.FStarC_Syntax_Syntax.ppname);
                           FStarC_Syntax_Syntax.index =
                             (x.FStarC_Syntax_Syntax.index);
                           FStarC_Syntax_Syntax.sort = ty
                         } in
                     FStarC_TypeChecker_Cfg.log cfg
                       (fun uu___7 ->
                          FStarC_Format.print_string
                            "+++ Normalizing Tm_let -- definiens\n");
                     (let lb1 =
                        let uu___7 =
                          norm cfg env1 [] lb.FStarC_Syntax_Syntax.lbdef in
                        let uu___8 =
                          FStarC_List.map (norm cfg env1 [])
                            lb.FStarC_Syntax_Syntax.lbattrs in
                        {
                          FStarC_Syntax_Syntax.lbname = lbname;
                          FStarC_Syntax_Syntax.lbunivs =
                            (lb.FStarC_Syntax_Syntax.lbunivs);
                          FStarC_Syntax_Syntax.lbtyp = ty;
                          FStarC_Syntax_Syntax.lbeff =
                            (lb.FStarC_Syntax_Syntax.lbeff);
                          FStarC_Syntax_Syntax.lbdef = uu___7;
                          FStarC_Syntax_Syntax.lbattrs = uu___8;
                          FStarC_Syntax_Syntax.lbpos =
                            (lb.FStarC_Syntax_Syntax.lbpos)
                        } in
                      let env' =
                        FStarC_List.fold_left
                          (fun env2 uu___7 ->
                             let uu___8 = dummy () in uu___8 :: env2) env1 bs in
                      FStarC_TypeChecker_Cfg.log cfg
                        (fun uu___8 ->
                           FStarC_Format.print_string
                             "+++ Normalizing Tm_let -- body\n");
                      (let cfg' =
                         {
                           FStarC_TypeChecker_Cfg.steps =
                             (cfg.FStarC_TypeChecker_Cfg.steps);
                           FStarC_TypeChecker_Cfg.tcenv =
                             (cfg.FStarC_TypeChecker_Cfg.tcenv);
                           FStarC_TypeChecker_Cfg.debug =
                             (cfg.FStarC_TypeChecker_Cfg.debug);
                           FStarC_TypeChecker_Cfg.delta_level =
                             (cfg.FStarC_TypeChecker_Cfg.delta_level);
                           FStarC_TypeChecker_Cfg.primitive_steps =
                             (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
                           FStarC_TypeChecker_Cfg.strong = true;
                           FStarC_TypeChecker_Cfg.memoize_lazy =
                             (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
                           FStarC_TypeChecker_Cfg.normalize_pure_lets =
                             (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
                           FStarC_TypeChecker_Cfg.reifying =
                             (cfg.FStarC_TypeChecker_Cfg.reifying);
                           FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                             (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                         } in
                       let body_norm =
                         norm cfg' env'
                           [Let
                              (env1, bs, lb1, (t1.FStarC_Syntax_Syntax.pos))]
                           body1 in
                       rebuild cfg env1 stack2 body_norm))))))
   | FStarC_Syntax_Syntax.Tm_let
       { FStarC_Syntax_Syntax.lbs = (true, lbs);
         FStarC_Syntax_Syntax.body1 = body;_}
       when should_reify cfg stack2 ->
       let rec strip_reify s =
         match s with
         | (App
             (uu___2,
              {
                FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                  (FStarC_Const.Const_reify lopt);
                FStarC_Syntax_Syntax.pos = uu___3;
                FStarC_Syntax_Syntax.hash_code = uu___4;_},
              uu___5, uu___6))::s1
             -> (lopt, s1)
         | (MemoLazy uu___2)::s' ->
             let uu___3 = strip_reify s' in
             (match uu___3 with
              | (lopt, s'1) -> (lopt, ((FStarC_List.hd s) :: s'1)))
         | (UnivArgs uu___2)::s' ->
             let uu___3 = strip_reify s' in
             (match uu___3 with
              | (lopt, s'1) -> (lopt, ((FStarC_List.hd s) :: s'1)))
         | uu___2 ->
             FStarC_Effect.failwith
               "impossible: should_reify but no reify on the stack" in
       let uu___2 = strip_reify stack2 in
       (match uu___2 with
        | (lopt, stack3) ->
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 = FStarC_Syntax_Util.mk_reify body lopt in
                  {
                    FStarC_Syntax_Syntax.lbs = (true, lbs);
                    FStarC_Syntax_Syntax.body1 = uu___6
                  } in
                FStarC_Syntax_Syntax.Tm_let uu___5 in
              {
                FStarC_Syntax_Syntax.n = uu___4;
                FStarC_Syntax_Syntax.pos = (t1.FStarC_Syntax_Syntax.pos);
                FStarC_Syntax_Syntax.hash_code =
                  (t1.FStarC_Syntax_Syntax.hash_code)
              } in
            norm cfg env1 stack3 uu___3)
   | FStarC_Syntax_Syntax.Tm_let
       { FStarC_Syntax_Syntax.lbs = (true, lbs);
         FStarC_Syntax_Syntax.body1 = body;_}
       when
       (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.compress_uvars
         ||
         (((Prims.not
              (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta)
             &&
             (Prims.not
                (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta_full))
            &&
            (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.pure_subterms_within_computations)
       ->
       let uu___2 = FStarC_Syntax_Subst.open_let_rec lbs body in
       (match uu___2 with
        | (lbs1, body1) ->
            let lbs2 =
              FStarC_List.map
                (fun lb ->
                   let ty = norm cfg env1 [] lb.FStarC_Syntax_Syntax.lbtyp in
                   let lbname =
                     FStar_Pervasives.Inl
                       (let uu___3 =
                          match lb.FStarC_Syntax_Syntax.lbname with
                          | FStar_Pervasives.Inl v -> v in
                        {
                          FStarC_Syntax_Syntax.ppname =
                            (uu___3.FStarC_Syntax_Syntax.ppname);
                          FStarC_Syntax_Syntax.index =
                            (uu___3.FStarC_Syntax_Syntax.index);
                          FStarC_Syntax_Syntax.sort = ty
                        }) in
                   let uu___3 =
                     FStarC_Syntax_Util.abs_formals
                       lb.FStarC_Syntax_Syntax.lbdef in
                   match uu___3 with
                   | (xs, def_body, lopt) ->
                       let xs1 = norm_binders cfg env1 xs in
                       let env2 =
                         let uu___4 =
                           FStarC_List.map (fun uu___5 -> dummy ()) xs1 in
                         let uu___5 =
                           let uu___6 =
                             FStarC_List.map (fun uu___7 -> dummy ()) lbs1 in
                           FStarC_List.op_At uu___6 env1 in
                         FStarC_List.op_At uu___4 uu___5 in
                       let def_body1 = norm cfg env2 [] def_body in
                       let lopt1 =
                         match lopt with
                         | FStar_Pervasives_Native.Some rc ->
                             let uu___4 =
                               let uu___5 =
                                 FStarC_Option.map (norm cfg env2 [])
                                   rc.FStarC_Syntax_Syntax.residual_typ in
                               {
                                 FStarC_Syntax_Syntax.residual_effect =
                                   (rc.FStarC_Syntax_Syntax.residual_effect);
                                 FStarC_Syntax_Syntax.residual_typ = uu___5;
                                 FStarC_Syntax_Syntax.residual_flags =
                                   (rc.FStarC_Syntax_Syntax.residual_flags)
                               } in
                             FStar_Pervasives_Native.Some uu___4
                         | uu___4 -> lopt in
                       let def = FStarC_Syntax_Util.abs xs1 def_body1 lopt1 in
                       {
                         FStarC_Syntax_Syntax.lbname = lbname;
                         FStarC_Syntax_Syntax.lbunivs =
                           (lb.FStarC_Syntax_Syntax.lbunivs);
                         FStarC_Syntax_Syntax.lbtyp = ty;
                         FStarC_Syntax_Syntax.lbeff =
                           (lb.FStarC_Syntax_Syntax.lbeff);
                         FStarC_Syntax_Syntax.lbdef = def;
                         FStarC_Syntax_Syntax.lbattrs =
                           (lb.FStarC_Syntax_Syntax.lbattrs);
                         FStarC_Syntax_Syntax.lbpos =
                           (lb.FStarC_Syntax_Syntax.lbpos)
                       }) lbs1 in
            let env' =
              let uu___3 = FStarC_List.map (fun uu___4 -> dummy ()) lbs2 in
              FStarC_List.op_At uu___3 env1 in
            let body2 = norm cfg env' [] body1 in
            let uu___3 = FStarC_Syntax_Subst.close_let_rec lbs2 body2 in
            (match uu___3 with
             | (lbs3, body3) ->
                 let t2 =
                   {
                     FStarC_Syntax_Syntax.n =
                       (FStarC_Syntax_Syntax.Tm_let
                          {
                            FStarC_Syntax_Syntax.lbs = (true, lbs3);
                            FStarC_Syntax_Syntax.body1 = body3
                          });
                     FStarC_Syntax_Syntax.pos = (t1.FStarC_Syntax_Syntax.pos);
                     FStarC_Syntax_Syntax.hash_code =
                       (t1.FStarC_Syntax_Syntax.hash_code)
                   } in
                 rebuild cfg env1 stack2 t2))
   | FStarC_Syntax_Syntax.Tm_let
       { FStarC_Syntax_Syntax.lbs = lbs; FStarC_Syntax_Syntax.body1 = body;_}
       when
       (Prims.not
          (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta)
         &&
         (Prims.not
            (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta_full)
       ->
       let uu___2 = closure_as_term cfg env1 t1 in
       rebuild cfg env1 stack2 uu___2
   | FStarC_Syntax_Syntax.Tm_let
       { FStarC_Syntax_Syntax.lbs = lbs; FStarC_Syntax_Syntax.body1 = body;_}
       ->
       let uu___2 =
         FStarC_List.fold_right
           (fun lb uu___3 ->
              match uu___3 with
              | (env_elts, memos, i) ->
                  let bv =
                    let uu___4 =
                      match lb.FStarC_Syntax_Syntax.lbname with
                      | FStar_Pervasives.Inl v -> v in
                    {
                      FStarC_Syntax_Syntax.ppname =
                        (uu___4.FStarC_Syntax_Syntax.ppname);
                      FStarC_Syntax_Syntax.index = i;
                      FStarC_Syntax_Syntax.sort =
                        (uu___4.FStarC_Syntax_Syntax.sort)
                    } in
                  let f_i = FStarC_Syntax_Syntax.bv_to_tm bv in
                  let fix_f_i =
                    FStarC_Syntax_Syntax.mk
                      (FStarC_Syntax_Syntax.Tm_let
                         {
                           FStarC_Syntax_Syntax.lbs = lbs;
                           FStarC_Syntax_Syntax.body1 = f_i
                         }) t1.FStarC_Syntax_Syntax.pos in
                  let memo = fresh_cfg_memo () in
                  let env_elts1 =
                    let uu___4 =
                      let uu___5 = fresh_memo () in
                      (FStar_Pervasives_Native.None,
                        (Clos (env1, fix_f_i, memo, true)), uu___5) in
                    uu___4 :: env_elts in
                  (env_elts1, (memo :: memos), (i + Prims.int_one)))
           (FStar_Pervasives_Native.snd lbs) ([], [], Prims.int_zero) in
       (match uu___2 with
        | (env_elts, memos, uu___3) ->
            let rec_env = FStarC_List.op_At (FStarC_List.rev env_elts) env1 in
            let uu___4 =
              FStarC_List.map2
                (fun lb memo ->
                   FStarC_Effect.op_Colon_Equals (memo_cell cfg memo)
                     (FStar_Pervasives_Native.Some
                        (cfg, (rec_env, (lb.FStarC_Syntax_Syntax.lbdef)))))
                (FStar_Pervasives_Native.snd lbs) memos in
            let body_env =
              FStarC_List.fold_left
                (fun env2 lb ->
                   let uu___5 =
                     let uu___6 =
                       let uu___7 =
                         let uu___8 = fresh_cfg_memo () in
                         (rec_env, (lb.FStarC_Syntax_Syntax.lbdef), uu___8,
                           false) in
                       Clos uu___7 in
                     let uu___7 = fresh_memo () in
                     (FStar_Pervasives_Native.None, uu___6, uu___7) in
                   uu___5 :: env2) env1 (FStar_Pervasives_Native.snd lbs) in
            (FStarC_TypeChecker_Cfg.log cfg
               (fun uu___6 ->
                  FStarC_Format.print1 "reducing with knot %s\n" "");
             norm cfg body_env stack2 body))
   | FStarC_Syntax_Syntax.Tm_meta
       { FStarC_Syntax_Syntax.tm2 = head; FStarC_Syntax_Syntax.meta = m;_} ->
       (FStarC_TypeChecker_Cfg.log cfg
          (fun uu___3 ->
             let uu___4 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_metadata m in
             FStarC_Format.print1 ">> metadata = %s\n" uu___4);
        (match m with
         | FStarC_Syntax_Syntax.Meta_monadic (m_from, ty) ->
             if
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
             then
               let uu___3 =
                 let uu___4 =
                   FStarC_TypeChecker_Env.is_erasable_effect
                     cfg.FStarC_TypeChecker_Cfg.tcenv m_from in
                 if uu___4
                 then true
                 else
                   if FStarC_Syntax_Util.is_pure_effect m_from
                   then
                     FStarC_TypeChecker_Env.non_informative
                       cfg.FStarC_TypeChecker_Cfg.tcenv ty
                   else false in
               (if uu___3
                then
                  let uu___4 =
                    FStarC_Syntax_Syntax.mk
                      (FStarC_Syntax_Syntax.Tm_meta
                         {
                           FStarC_Syntax_Syntax.tm2 =
                             FStarC_Syntax_Util.exp_unit;
                           FStarC_Syntax_Syntax.meta = m
                         }) t1.FStarC_Syntax_Syntax.pos in
                  rebuild cfg env1 stack2 uu___4
                else
                  reduce_impure_comp cfg env1 stack2 head
                    (FStar_Pervasives.Inl m_from) ty)
             else
               reduce_impure_comp cfg env1 stack2 head
                 (FStar_Pervasives.Inl m_from) ty
         | FStarC_Syntax_Syntax.Meta_monadic_lift (m_from, m_to, ty) ->
             if
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
             then
               let uu___3 =
                 let uu___4 =
                   let uu___5 =
                     FStarC_TypeChecker_Env.is_erasable_effect
                       cfg.FStarC_TypeChecker_Cfg.tcenv m_from in
                   if uu___5
                   then true
                   else
                     FStarC_TypeChecker_Env.is_erasable_effect
                       cfg.FStarC_TypeChecker_Cfg.tcenv m_to in
                 if uu___4
                 then true
                 else
                   if FStarC_Syntax_Util.is_pure_effect m_from
                   then
                     FStarC_TypeChecker_Env.non_informative
                       cfg.FStarC_TypeChecker_Cfg.tcenv ty
                   else false in
               (if uu___3
                then
                  let uu___4 =
                    FStarC_Syntax_Syntax.mk
                      (FStarC_Syntax_Syntax.Tm_meta
                         {
                           FStarC_Syntax_Syntax.tm2 =
                             FStarC_Syntax_Util.exp_unit;
                           FStarC_Syntax_Syntax.meta = m
                         }) t1.FStarC_Syntax_Syntax.pos in
                  rebuild cfg env1 stack2 uu___4
                else
                  reduce_impure_comp cfg env1 stack2 head
                    (FStar_Pervasives.Inr (m_from, m_to)) ty)
             else
               reduce_impure_comp cfg env1 stack2 head
                 (FStar_Pervasives.Inr (m_from, m_to)) ty
         | uu___3 ->
             if
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unmeta
             then norm cfg env1 stack2 head
             else
               (match stack2 with
                | uu___4::uu___5 ->
                    (match m with
                     | FStarC_Syntax_Syntax.Meta_labeled (l, r, uu___6) ->
                         norm cfg env1 ((Meta (env1, m, r)) :: stack2) head
                     | FStarC_Syntax_Syntax.Meta_pattern (names, args) ->
                         let args1 = norm_pattern_args cfg env1 args in
                         let names1 =
                           FStarC_List.map (norm cfg env1 []) names in
                         norm cfg env1
                           ((Meta
                               (env1,
                                 (FStarC_Syntax_Syntax.Meta_pattern
                                    (names1, args1)),
                                 (t1.FStarC_Syntax_Syntax.pos))) :: stack2)
                           head
                     | FStarC_Syntax_Syntax.Meta_desugared
                         (FStarC_Syntax_Syntax.Sequence) when
                         (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets
                         ->
                         norm cfg env1
                           ((Meta (env1, m, (t1.FStarC_Syntax_Syntax.pos)))
                           :: stack2) head
                     | FStarC_Syntax_Syntax.Meta_desugared
                         (FStarC_Syntax_Syntax.Machine_integer
                         (uu___6, uu___7)) ->
                         norm cfg env1
                           ((Meta (env1, m, (t1.FStarC_Syntax_Syntax.pos)))
                           :: stack2) head
                     | uu___6 -> norm cfg env1 stack2 head)
                | [] ->
                    let head1 = norm cfg env1 [] head in
                    let m1 =
                      match m with
                      | FStarC_Syntax_Syntax.Meta_pattern (names, args) ->
                          let names1 =
                            FStarC_List.map (norm cfg env1 []) names in
                          let uu___4 =
                            let uu___5 = norm_pattern_args cfg env1 args in
                            (names1, uu___5) in
                          FStarC_Syntax_Syntax.Meta_pattern uu___4
                      | uu___4 -> m in
                    let t2 =
                      FStarC_Syntax_Syntax.mk
                        (FStarC_Syntax_Syntax.Tm_meta
                           {
                             FStarC_Syntax_Syntax.tm2 = head1;
                             FStarC_Syntax_Syntax.meta = m1
                           }) t1.FStarC_Syntax_Syntax.pos in
                    rebuild cfg env1 stack2 t2)))
   | FStarC_Syntax_Syntax.Tm_delayed uu___2 ->
       FStarC_Effect.failwith "impossible: Tm_delayed on norm"
   | FStarC_Syntax_Syntax.Tm_uvar uu___2 ->
       (if
          (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.check_no_uvars
        then
          (let uu___4 =
             let uu___5 =
               FStarC_Class_Show.show FStarC_Range_Ops.showable_range
                 t1.FStarC_Syntax_Syntax.pos in
             let uu___6 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
             FStarC_Format.fmt2
               "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
               uu___5 uu___6 in
           FStarC_Effect.failwith uu___4)
        else ();
        (let t2 =
           FStarC_Errors.with_ctx "inlining"
             (fun uu___4 -> closure_as_term cfg env1 t1) in
         rebuild cfg env1 stack2 t2)))
and do_unfold_fv (cfg : FStarC_TypeChecker_Cfg.cfg) (stack1 : stack)
  (t0 : FStarC_Syntax_Syntax.term) (qninfo : FStarC_TypeChecker_Env.qninfo)
  (f : FStarC_Syntax_Syntax.fv) : FStarC_Syntax_Syntax.term=
  let defn uu___ =
    FStarC_TypeChecker_Env.lookup_definition_qninfo
      cfg.FStarC_TypeChecker_Cfg.delta_level f.FStarC_Syntax_Syntax.fv_name
      qninfo in
  let is_plugin uu___ =
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Pervasives.Inr (se, FStar_Pervasives_Native.None), uu___1) ->
        FStarC_Util.for_some
          (FStarC_Syntax_Util.is_fvar FStarC_Parser_Const.plugin_attr)
          se.FStarC_Syntax_Syntax.sigattrs
    | uu___1 -> false in
  let maybe_warn_if_unfolding_plugin uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          if
            match (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.dont_unfold_attr
            with
            | FStar_Pervasives_Native.Some v -> true
            | uu___4 -> false
          then let uu___4 = FStarC_Options.no_plugins () in Prims.not uu___4
          else false in
        if uu___3
        then
          let uu___4 = FStarC_Effect.op_Bang plugin_unfold_warn_ctr in
          uu___4 > Prims.int_zero
        else false in
      if uu___2 then is_plugin () else false in
    if uu___1
    then
      let msg =
        let uu___2 =
          FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_fv f in
        FStarC_Format.fmt1 "Unfolding name which is marked as a plugin: %s"
          uu___2 in
      (FStarC_Errors.log_issue FStarC_Syntax_Syntax.hasRange_fv f
         FStarC_Errors_Codes.Warning_UnfoldPlugin ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
         (Obj.magic msg);
       (let uu___3 =
          let uu___4 = FStarC_Effect.op_Bang plugin_unfold_warn_ctr in
          uu___4 - Prims.int_one in
        FStarC_Effect.op_Colon_Equals plugin_unfold_warn_ctr uu___3))
    else () in
  let defn1 uu___ =
    if
      (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
    then
      match qninfo with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr (se, FStar_Pervasives_Native.None), uu___1)
          when
          FStarC_TypeChecker_Env.visible_with
            cfg.FStarC_TypeChecker_Cfg.delta_level
            se.FStarC_Syntax_Syntax.sigquals
          ->
          let uu___2 =
            FStarC_Util.find_map se.FStarC_Syntax_Syntax.sigattrs
              FStarC_Parser_Const_ExtractAs.is_extract_as_attr in
          (match uu___2 with
           | FStar_Pervasives_Native.Some impl ->
               FStar_Pervasives_Native.Some ([], impl)
           | FStar_Pervasives_Native.None -> defn ())
      | uu___1 -> defn ()
    else defn () in
  let uu___ = defn1 () in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      (FStarC_TypeChecker_Cfg.log_unfolding cfg
         (fun uu___2 ->
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_fv f in
            let uu___4 =
              FStarC_Class_Show.show
                (FStarC_Class_Show.show_list
                   FStarC_TypeChecker_Env.showable_delta_level)
                cfg.FStarC_TypeChecker_Cfg.delta_level in
            FStarC_Format.print2
              " >> No definition found for %s (delta_level = %s)\n" uu___3
              uu___4);
       rebuild cfg empty_env stack1 t0)
  | FStar_Pervasives_Native.Some (us, t) ->
      (FStarC_TypeChecker_Cfg.log_unfolding cfg
         (fun uu___2 ->
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t0 in
            let uu___4 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
            FStarC_Format.print2 " >> Unfolded %s to %s\n" uu___3 uu___4);
       maybe_warn_if_unfolding_plugin ();
       (let t1 =
          if
            (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_until
              =
              (FStar_Pervasives_Native.Some
                 FStarC_Syntax_Syntax.delta_constant)
          then t
          else
            FStarC_Syntax_Subst.set_use_range t0.FStarC_Syntax_Syntax.pos t in
        let n = FStarC_List.length us in
        if n > Prims.int_zero
        then
          match stack1 with
          | (UnivArgs (us', uu___3))::stack2 ->
              ((let uu___5 = FStarC_Effect.op_Bang dbg_univ_norm in
                if uu___5
                then
                  FStarC_List.iter
                    (fun x ->
                       let uu___6 =
                         FStarC_Class_Show.show
                           FStarC_Syntax_Print.showable_univ x in
                       FStarC_Format.print1 "Univ (normalizer) %s\n" uu___6)
                    us'
                else ());
               (let env1 =
                  FStarC_List.fold_left
                    (fun env2 u ->
                       let uu___5 =
                         let uu___6 = fresh_memo () in
                         (FStar_Pervasives_Native.None, (Univ u), uu___6) in
                       uu___5 :: env2) empty_env us' in
                norm cfg env1 stack2 t1))
          | uu___3 when
              (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.erase_universes
                ||
                (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.allow_unbound_universes
              -> norm cfg empty_env stack1 t1
          | uu___3 ->
              let uu___4 =
                let uu___5 =
                  FStarC_Class_Show.show FStarC_Ident.showable_lident
                    f.FStarC_Syntax_Syntax.fv_name in
                FStarC_Format.fmt1
                  "Impossible: missing universe instantiation on %s" uu___5 in
              FStarC_Effect.failwith uu___4
        else norm cfg empty_env stack1 t1))
and handle_norm_request (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (stack1 : stack_elt Prims.list) (k : norm_request_kind)
  (hd : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let debug =
    (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.print_normalized in
  if debug
  then
    (let uu___1 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term hd in
     let uu___2 =
       FStarC_Class_Show.show
         (FStarC_Class_Show.show_list showable_stack_elt)
         (FStar_Pervasives_Native.fst (firstn (Prims.of_int 5) stack1)) in
     FStarC_Format.print2 "handle_norm_request %s, stack = %s\n" uu___1
       uu___2)
  else ();
  (let inherited_steps =
     FStarC_List.op_At
       (if
          (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.erase_universes
        then [FStarC_TypeChecker_Env.EraseUniverses]
        else [])
       (FStarC_List.op_At
          (if
             (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.allow_unbound_universes
           then [FStarC_TypeChecker_Env.AllowUnboundUniverses]
           else [])
          (if
             (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.nbe_step
           then [FStarC_TypeChecker_Env.NBE]
           else [])) in
   let parse_steps s =
     let uu___1 =
       FStarC_TypeChecker_Primops_Base.try_unembed_simple
         (FStarC_Syntax_Embeddings.e_list
            FStarC_Syntax_Embeddings.e_norm_step) s in
     match uu___1 with
     | FStar_Pervasives_Native.Some steps ->
         let uu___2 = FStarC_TypeChecker_Cfg.translate_norm_steps steps in
         FStar_Pervasives_Native.Some uu___2
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
   let env_term_steps_stack =
     match (k, stack1) with
     | (NormalizeTerm, (UnivArgs uu___1)::(Arg
        (Clos (uu___2, uu___3, uu___4, uu___5), uu___6, uu___7))::(Arg
        (Clos (a_env, a_t, uu___8, uu___9), uu___10, uu___11))::stack') ->
         let steps =
           [FStarC_TypeChecker_Env.Beta;
           FStarC_TypeChecker_Env.Zeta;
           FStarC_TypeChecker_Env.Iota;
           FStarC_TypeChecker_Env.Primops;
           FStarC_TypeChecker_Env.UnfoldUntil
             FStarC_Syntax_Syntax.delta_constant;
           FStarC_TypeChecker_Env.Reify] in
         let steps1 =
           FStarC_List.op_At
             ((FStarC_TypeChecker_Env.DontUnfoldAttr
                 [FStarC_Parser_Const.tac_opaque_attr]) :: inherited_steps)
             steps in
         ((FStar_Pervasives_Native.Some (a_env, a_t, steps1)), stack')
     | (NormalizeTerm, (Arg
        (Clos (uu___1, uu___2, uu___3, uu___4), uu___5, uu___6))::(Arg
        (Clos (a_env, a_t, uu___7, uu___8), uu___9, uu___10))::stack') ->
         let steps =
           [FStarC_TypeChecker_Env.Beta;
           FStarC_TypeChecker_Env.Zeta;
           FStarC_TypeChecker_Env.Iota;
           FStarC_TypeChecker_Env.Primops;
           FStarC_TypeChecker_Env.UnfoldUntil
             FStarC_Syntax_Syntax.delta_constant;
           FStarC_TypeChecker_Env.Reify] in
         let steps1 =
           FStarC_List.op_At
             ((FStarC_TypeChecker_Env.DontUnfoldAttr
                 [FStarC_Parser_Const.tac_opaque_attr]) :: inherited_steps)
             steps in
         ((FStar_Pervasives_Native.Some (a_env, a_t, steps1)), stack')
     | (Normalize, (Arg
        (Clos (a_env, a_t, uu___1, uu___2), uu___3, uu___4))::stack') ->
         let steps =
           [FStarC_TypeChecker_Env.Beta;
           FStarC_TypeChecker_Env.Zeta;
           FStarC_TypeChecker_Env.Iota;
           FStarC_TypeChecker_Env.Primops;
           FStarC_TypeChecker_Env.UnfoldUntil
             FStarC_Syntax_Syntax.delta_constant;
           FStarC_TypeChecker_Env.Reify] in
         let steps1 =
           FStarC_List.op_At
             ((FStarC_TypeChecker_Env.DontUnfoldAttr
                 [FStarC_Parser_Const.tac_opaque_attr]) :: inherited_steps)
             steps in
         ((FStar_Pervasives_Native.Some (a_env, a_t, steps1)), stack')
     | (Norm, (UnivArgs uu___1)::(Arg
        (Clos (s_env, s_t, uu___2, uu___3), uu___4, uu___5))::(Arg
        (Clos (uu___6, uu___7, uu___8, uu___9), uu___10, uu___11))::(Arg
        (Clos (a_env, a_t, uu___12, uu___13), uu___14, uu___15))::stack') ->
         let cfg' =
           {
             FStarC_TypeChecker_Cfg.steps =
               (let uu___16 = cfg.FStarC_TypeChecker_Cfg.steps in
                {
                  FStarC_TypeChecker_Cfg.beta =
                    (uu___16.FStarC_TypeChecker_Cfg.beta);
                  FStarC_TypeChecker_Cfg.iota =
                    (uu___16.FStarC_TypeChecker_Cfg.iota);
                  FStarC_TypeChecker_Cfg.zeta =
                    (uu___16.FStarC_TypeChecker_Cfg.zeta);
                  FStarC_TypeChecker_Cfg.zeta_full =
                    (uu___16.FStarC_TypeChecker_Cfg.zeta_full);
                  FStarC_TypeChecker_Cfg.weak =
                    (uu___16.FStarC_TypeChecker_Cfg.weak);
                  FStarC_TypeChecker_Cfg.hnf =
                    (uu___16.FStarC_TypeChecker_Cfg.hnf);
                  FStarC_TypeChecker_Cfg.primops =
                    (uu___16.FStarC_TypeChecker_Cfg.primops);
                  FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets = false;
                  FStarC_TypeChecker_Cfg.unfold_until =
                    (uu___16.FStarC_TypeChecker_Cfg.unfold_until);
                  FStarC_TypeChecker_Cfg.unfold_only =
                    FStar_Pervasives_Native.None;
                  FStarC_TypeChecker_Cfg.unfold_once =
                    (uu___16.FStarC_TypeChecker_Cfg.unfold_once);
                  FStarC_TypeChecker_Cfg.unfold_fully =
                    FStar_Pervasives_Native.None;
                  FStarC_TypeChecker_Cfg.unfold_attr =
                    (uu___16.FStarC_TypeChecker_Cfg.unfold_attr);
                  FStarC_TypeChecker_Cfg.unfold_qual =
                    (uu___16.FStarC_TypeChecker_Cfg.unfold_qual);
                  FStarC_TypeChecker_Cfg.unfold_namespace =
                    (uu___16.FStarC_TypeChecker_Cfg.unfold_namespace);
                  FStarC_TypeChecker_Cfg.dont_unfold_attr =
                    (uu___16.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                  FStarC_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___16.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStarC_TypeChecker_Cfg.simplify =
                    (uu___16.FStarC_TypeChecker_Cfg.simplify);
                  FStarC_TypeChecker_Cfg.erase_universes =
                    (uu___16.FStarC_TypeChecker_Cfg.erase_universes);
                  FStarC_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___16.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                  FStarC_TypeChecker_Cfg.reify_ =
                    (uu___16.FStarC_TypeChecker_Cfg.reify_);
                  FStarC_TypeChecker_Cfg.compress_uvars =
                    (uu___16.FStarC_TypeChecker_Cfg.compress_uvars);
                  FStarC_TypeChecker_Cfg.no_full_norm =
                    (uu___16.FStarC_TypeChecker_Cfg.no_full_norm);
                  FStarC_TypeChecker_Cfg.check_no_uvars =
                    (uu___16.FStarC_TypeChecker_Cfg.check_no_uvars);
                  FStarC_TypeChecker_Cfg.unmeta =
                    (uu___16.FStarC_TypeChecker_Cfg.unmeta);
                  FStarC_TypeChecker_Cfg.unascribe =
                    (uu___16.FStarC_TypeChecker_Cfg.unascribe);
                  FStarC_TypeChecker_Cfg.in_full_norm_request =
                    (uu___16.FStarC_TypeChecker_Cfg.in_full_norm_request);
                  FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___16.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStarC_TypeChecker_Cfg.nbe_step =
                    (uu___16.FStarC_TypeChecker_Cfg.nbe_step);
                  FStarC_TypeChecker_Cfg.for_extraction =
                    (uu___16.FStarC_TypeChecker_Cfg.for_extraction);
                  FStarC_TypeChecker_Cfg.unrefine =
                    (uu___16.FStarC_TypeChecker_Cfg.unrefine);
                  FStarC_TypeChecker_Cfg.default_univs_to_zero =
                    (uu___16.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                  FStarC_TypeChecker_Cfg.tactics =
                    (uu___16.FStarC_TypeChecker_Cfg.tactics);
                  FStarC_TypeChecker_Cfg.reduce_projections =
                    (uu___16.FStarC_TypeChecker_Cfg.reduce_projections)
                });
             FStarC_TypeChecker_Cfg.tcenv =
               (cfg.FStarC_TypeChecker_Cfg.tcenv);
             FStarC_TypeChecker_Cfg.debug =
               (cfg.FStarC_TypeChecker_Cfg.debug);
             FStarC_TypeChecker_Cfg.delta_level =
               [FStarC_TypeChecker_Env.Unfold
                  FStarC_Syntax_Syntax.delta_constant];
             FStarC_TypeChecker_Cfg.primitive_steps =
               (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
             FStarC_TypeChecker_Cfg.strong =
               (cfg.FStarC_TypeChecker_Cfg.strong);
             FStarC_TypeChecker_Cfg.memoize_lazy =
               (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
             FStarC_TypeChecker_Cfg.normalize_pure_lets = true;
             FStarC_TypeChecker_Cfg.reifying =
               (cfg.FStarC_TypeChecker_Cfg.reifying);
             FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
               (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
           } in
         let s_t1 = norm cfg' s_env [] s_t in
         let uu___16 = parse_steps s_t1 in
         (match uu___16 with
          | FStar_Pervasives_Native.Some s ->
              let s1 =
                FStarC_List.op_At
                  ((FStarC_TypeChecker_Env.DontUnfoldAttr
                      [FStarC_Parser_Const.tac_opaque_attr]) ::
                  inherited_steps) s in
              ((FStar_Pervasives_Native.Some (a_env, a_t, s1)), stack')
          | FStar_Pervasives_Native.None ->
              (if debug
               then
                 (let uu___18 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      s_t1 in
                  let uu___19 =
                    FStarC_Class_Show.show
                      (FStarC_Class_Show.show_list
                         (FStarC_Class_Show.show_tuple3
                            (FStarC_Class_Show.show_option
                               FStarC_Syntax_Print.showable_binder)
                            showable_closure
                            (showable_memo
                               (FStarC_Class_Show.show_list
                                  FStarC_Syntax_Print.showable_subst_elt))))
                      s_env in
                  FStarC_Format.print2
                    "handle_norm_request: couldn't parse steps %s in env %s\n"
                    uu___18 uu___19)
               else ();
               (FStar_Pervasives_Native.None, stack1)))
     | (Norm, (Arg (Clos (s_env, s_t, uu___1, uu___2), uu___3, uu___4))::(Arg
        (Clos (uu___5, uu___6, uu___7, uu___8), uu___9, uu___10))::(Arg
        (Clos (a_env, a_t, uu___11, uu___12), uu___13, uu___14))::stack') ->
         let cfg' =
           {
             FStarC_TypeChecker_Cfg.steps =
               (let uu___15 = cfg.FStarC_TypeChecker_Cfg.steps in
                {
                  FStarC_TypeChecker_Cfg.beta =
                    (uu___15.FStarC_TypeChecker_Cfg.beta);
                  FStarC_TypeChecker_Cfg.iota =
                    (uu___15.FStarC_TypeChecker_Cfg.iota);
                  FStarC_TypeChecker_Cfg.zeta =
                    (uu___15.FStarC_TypeChecker_Cfg.zeta);
                  FStarC_TypeChecker_Cfg.zeta_full =
                    (uu___15.FStarC_TypeChecker_Cfg.zeta_full);
                  FStarC_TypeChecker_Cfg.weak =
                    (uu___15.FStarC_TypeChecker_Cfg.weak);
                  FStarC_TypeChecker_Cfg.hnf =
                    (uu___15.FStarC_TypeChecker_Cfg.hnf);
                  FStarC_TypeChecker_Cfg.primops =
                    (uu___15.FStarC_TypeChecker_Cfg.primops);
                  FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets = false;
                  FStarC_TypeChecker_Cfg.unfold_until =
                    (uu___15.FStarC_TypeChecker_Cfg.unfold_until);
                  FStarC_TypeChecker_Cfg.unfold_only =
                    FStar_Pervasives_Native.None;
                  FStarC_TypeChecker_Cfg.unfold_once =
                    (uu___15.FStarC_TypeChecker_Cfg.unfold_once);
                  FStarC_TypeChecker_Cfg.unfold_fully =
                    FStar_Pervasives_Native.None;
                  FStarC_TypeChecker_Cfg.unfold_attr =
                    (uu___15.FStarC_TypeChecker_Cfg.unfold_attr);
                  FStarC_TypeChecker_Cfg.unfold_qual =
                    (uu___15.FStarC_TypeChecker_Cfg.unfold_qual);
                  FStarC_TypeChecker_Cfg.unfold_namespace =
                    (uu___15.FStarC_TypeChecker_Cfg.unfold_namespace);
                  FStarC_TypeChecker_Cfg.dont_unfold_attr =
                    (uu___15.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                  FStarC_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___15.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStarC_TypeChecker_Cfg.simplify =
                    (uu___15.FStarC_TypeChecker_Cfg.simplify);
                  FStarC_TypeChecker_Cfg.erase_universes =
                    (uu___15.FStarC_TypeChecker_Cfg.erase_universes);
                  FStarC_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___15.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                  FStarC_TypeChecker_Cfg.reify_ =
                    (uu___15.FStarC_TypeChecker_Cfg.reify_);
                  FStarC_TypeChecker_Cfg.compress_uvars =
                    (uu___15.FStarC_TypeChecker_Cfg.compress_uvars);
                  FStarC_TypeChecker_Cfg.no_full_norm =
                    (uu___15.FStarC_TypeChecker_Cfg.no_full_norm);
                  FStarC_TypeChecker_Cfg.check_no_uvars =
                    (uu___15.FStarC_TypeChecker_Cfg.check_no_uvars);
                  FStarC_TypeChecker_Cfg.unmeta =
                    (uu___15.FStarC_TypeChecker_Cfg.unmeta);
                  FStarC_TypeChecker_Cfg.unascribe =
                    (uu___15.FStarC_TypeChecker_Cfg.unascribe);
                  FStarC_TypeChecker_Cfg.in_full_norm_request =
                    (uu___15.FStarC_TypeChecker_Cfg.in_full_norm_request);
                  FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___15.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStarC_TypeChecker_Cfg.nbe_step =
                    (uu___15.FStarC_TypeChecker_Cfg.nbe_step);
                  FStarC_TypeChecker_Cfg.for_extraction =
                    (uu___15.FStarC_TypeChecker_Cfg.for_extraction);
                  FStarC_TypeChecker_Cfg.unrefine =
                    (uu___15.FStarC_TypeChecker_Cfg.unrefine);
                  FStarC_TypeChecker_Cfg.default_univs_to_zero =
                    (uu___15.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                  FStarC_TypeChecker_Cfg.tactics =
                    (uu___15.FStarC_TypeChecker_Cfg.tactics);
                  FStarC_TypeChecker_Cfg.reduce_projections =
                    (uu___15.FStarC_TypeChecker_Cfg.reduce_projections)
                });
             FStarC_TypeChecker_Cfg.tcenv =
               (cfg.FStarC_TypeChecker_Cfg.tcenv);
             FStarC_TypeChecker_Cfg.debug =
               (cfg.FStarC_TypeChecker_Cfg.debug);
             FStarC_TypeChecker_Cfg.delta_level =
               [FStarC_TypeChecker_Env.Unfold
                  FStarC_Syntax_Syntax.delta_constant];
             FStarC_TypeChecker_Cfg.primitive_steps =
               (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
             FStarC_TypeChecker_Cfg.strong =
               (cfg.FStarC_TypeChecker_Cfg.strong);
             FStarC_TypeChecker_Cfg.memoize_lazy =
               (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
             FStarC_TypeChecker_Cfg.normalize_pure_lets = true;
             FStarC_TypeChecker_Cfg.reifying =
               (cfg.FStarC_TypeChecker_Cfg.reifying);
             FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
               (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
           } in
         let s_t1 = norm cfg' s_env [] s_t in
         let uu___15 = parse_steps s_t1 in
         (match uu___15 with
          | FStar_Pervasives_Native.Some s ->
              let s1 =
                FStarC_List.op_At
                  ((FStarC_TypeChecker_Env.DontUnfoldAttr
                      [FStarC_Parser_Const.tac_opaque_attr]) ::
                  inherited_steps) s in
              ((FStar_Pervasives_Native.Some (a_env, a_t, s1)), stack')
          | FStar_Pervasives_Native.None ->
              (if debug
               then
                 (let uu___17 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      s_t1 in
                  let uu___18 =
                    FStarC_Class_Show.show
                      (FStarC_Class_Show.show_list
                         (FStarC_Class_Show.show_tuple3
                            (FStarC_Class_Show.show_option
                               FStarC_Syntax_Print.showable_binder)
                            showable_closure
                            (showable_memo
                               (FStarC_Class_Show.show_list
                                  FStarC_Syntax_Print.showable_subst_elt))))
                      s_env in
                  FStarC_Format.print2
                    "handle_norm_request: couldn't parse steps %s in env %s\n"
                    uu___17 uu___18)
               else ();
               (FStar_Pervasives_Native.None, stack1)))
     | uu___1 -> (FStar_Pervasives_Native.None, stack1) in
   match env_term_steps_stack with
   | (FStar_Pervasives_Native.None, stack2) ->
       (if debug
        then
          (let uu___2 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term hd in
           let uu___3 =
             FStarC_Class_Show.show
               (FStarC_Class_Show.show_list showable_stack_elt) stack2 in
           FStarC_Format.print2
             "Couldn't recognize norm request %s;; stack = %s\n" uu___2
             uu___3)
        else ();
        rebuild cfg env1 stack2 hd)
   | (FStar_Pervasives_Native.Some (t_env, tm, s), stack2) when
       is_nbe_request s ->
       let tm' = closure_as_term cfg t_env tm in
       let uu___1 =
         FStarC_Timing.record_ms (fun uu___2 -> nbe_eval cfg s tm') in
       (match uu___1 with
        | (tm_norm, elapsed) ->
            (if debug
             then
               (let cfg' =
                  FStarC_TypeChecker_Cfg.config s
                    cfg.FStarC_TypeChecker_Cfg.tcenv in
                let uu___3 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_int
                    elapsed in
                let uu___4 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                    tm' in
                let uu___5 =
                  FStarC_Class_Show.show FStarC_TypeChecker_Cfg.showable_cfg
                    cfg' in
                let uu___6 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                    tm_norm in
                FStarC_Format.print4
                  "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                  uu___3 uu___4 uu___5 uu___6)
             else ();
             rebuild cfg env1 stack2 tm_norm))
   | (FStar_Pervasives_Native.Some (t_env, tm, s), stack2) ->
       (if debug
        then
          (let uu___2 =
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     tm in
                 FStarC_Format.fmt1 "Starting norm request on `%s`." uu___5 in
               FStarC_Errors_Msg.text uu___4 in
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   let uu___7 =
                     FStarC_Class_Show.show
                       (FStarC_Class_Show.show_list
                          FStarC_TypeChecker_Env.showable_step) s in
                   FStarC_Errors_Msg.text uu___7 in
                 FStar_Pprint.op_Hat_Slash_Hat
                   (FStarC_Errors_Msg.text "Steps =") uu___6 in
               [uu___5] in
             uu___3 :: uu___4 in
           FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
             tm.FStarC_Syntax_Syntax.pos ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
             (Obj.magic uu___2))
        else ();
        (let delta_level =
           let uu___2 =
             FStarC_Util.for_some
               (fun uu___3 ->
                  match uu___3 with
                  | FStarC_TypeChecker_Env.UnfoldUntil uu___4 -> true
                  | FStarC_TypeChecker_Env.UnfoldOnly uu___4 -> true
                  | FStarC_TypeChecker_Env.UnfoldFully uu___4 -> true
                  | uu___4 -> false) s in
           if uu___2
           then
             [FStarC_TypeChecker_Env.Unfold
                FStarC_Syntax_Syntax.delta_constant]
           else
             if
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
             then
               [FStarC_TypeChecker_Env.Eager_unfolding_only;
               FStarC_TypeChecker_Env.InliningDelta]
             else [FStarC_TypeChecker_Env.NoDelta] in
         let cfg' =
           let uu___2 =
             let uu___3 = FStarC_TypeChecker_Cfg.to_fsteps s in
             {
               FStarC_TypeChecker_Cfg.beta =
                 (uu___3.FStarC_TypeChecker_Cfg.beta);
               FStarC_TypeChecker_Cfg.iota =
                 (uu___3.FStarC_TypeChecker_Cfg.iota);
               FStarC_TypeChecker_Cfg.zeta =
                 (uu___3.FStarC_TypeChecker_Cfg.zeta);
               FStarC_TypeChecker_Cfg.zeta_full =
                 (uu___3.FStarC_TypeChecker_Cfg.zeta_full);
               FStarC_TypeChecker_Cfg.weak =
                 (uu___3.FStarC_TypeChecker_Cfg.weak);
               FStarC_TypeChecker_Cfg.hnf =
                 (uu___3.FStarC_TypeChecker_Cfg.hnf);
               FStarC_TypeChecker_Cfg.primops =
                 (uu___3.FStarC_TypeChecker_Cfg.primops);
               FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                 (uu___3.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
               FStarC_TypeChecker_Cfg.unfold_until =
                 (uu___3.FStarC_TypeChecker_Cfg.unfold_until);
               FStarC_TypeChecker_Cfg.unfold_only =
                 (uu___3.FStarC_TypeChecker_Cfg.unfold_only);
               FStarC_TypeChecker_Cfg.unfold_once =
                 (uu___3.FStarC_TypeChecker_Cfg.unfold_once);
               FStarC_TypeChecker_Cfg.unfold_fully =
                 (uu___3.FStarC_TypeChecker_Cfg.unfold_fully);
               FStarC_TypeChecker_Cfg.unfold_attr =
                 (uu___3.FStarC_TypeChecker_Cfg.unfold_attr);
               FStarC_TypeChecker_Cfg.unfold_qual =
                 (uu___3.FStarC_TypeChecker_Cfg.unfold_qual);
               FStarC_TypeChecker_Cfg.unfold_namespace =
                 (uu___3.FStarC_TypeChecker_Cfg.unfold_namespace);
               FStarC_TypeChecker_Cfg.dont_unfold_attr =
                 (uu___3.FStarC_TypeChecker_Cfg.dont_unfold_attr);
               FStarC_TypeChecker_Cfg.pure_subterms_within_computations =
                 (uu___3.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
               FStarC_TypeChecker_Cfg.simplify =
                 (uu___3.FStarC_TypeChecker_Cfg.simplify);
               FStarC_TypeChecker_Cfg.erase_universes =
                 (uu___3.FStarC_TypeChecker_Cfg.erase_universes);
               FStarC_TypeChecker_Cfg.allow_unbound_universes =
                 (uu___3.FStarC_TypeChecker_Cfg.allow_unbound_universes);
               FStarC_TypeChecker_Cfg.reify_ =
                 (uu___3.FStarC_TypeChecker_Cfg.reify_);
               FStarC_TypeChecker_Cfg.compress_uvars =
                 (uu___3.FStarC_TypeChecker_Cfg.compress_uvars);
               FStarC_TypeChecker_Cfg.no_full_norm =
                 (uu___3.FStarC_TypeChecker_Cfg.no_full_norm);
               FStarC_TypeChecker_Cfg.check_no_uvars =
                 (uu___3.FStarC_TypeChecker_Cfg.check_no_uvars);
               FStarC_TypeChecker_Cfg.unmeta =
                 (uu___3.FStarC_TypeChecker_Cfg.unmeta);
               FStarC_TypeChecker_Cfg.unascribe =
                 (uu___3.FStarC_TypeChecker_Cfg.unascribe);
               FStarC_TypeChecker_Cfg.in_full_norm_request = true;
               FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                 (uu___3.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
               FStarC_TypeChecker_Cfg.nbe_step =
                 (uu___3.FStarC_TypeChecker_Cfg.nbe_step);
               FStarC_TypeChecker_Cfg.for_extraction =
                 ((cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction);
               FStarC_TypeChecker_Cfg.unrefine =
                 (uu___3.FStarC_TypeChecker_Cfg.unrefine);
               FStarC_TypeChecker_Cfg.default_univs_to_zero =
                 (uu___3.FStarC_TypeChecker_Cfg.default_univs_to_zero);
               FStarC_TypeChecker_Cfg.tactics =
                 (uu___3.FStarC_TypeChecker_Cfg.tactics);
               FStarC_TypeChecker_Cfg.reduce_projections =
                 (uu___3.FStarC_TypeChecker_Cfg.reduce_projections)
             } in
           {
             FStarC_TypeChecker_Cfg.steps = uu___2;
             FStarC_TypeChecker_Cfg.tcenv =
               (cfg.FStarC_TypeChecker_Cfg.tcenv);
             FStarC_TypeChecker_Cfg.debug =
               (cfg.FStarC_TypeChecker_Cfg.debug);
             FStarC_TypeChecker_Cfg.delta_level = delta_level;
             FStarC_TypeChecker_Cfg.primitive_steps =
               (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
             FStarC_TypeChecker_Cfg.strong =
               (cfg.FStarC_TypeChecker_Cfg.strong);
             FStarC_TypeChecker_Cfg.memoize_lazy =
               (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
             FStarC_TypeChecker_Cfg.normalize_pure_lets = true;
             FStarC_TypeChecker_Cfg.reifying =
               (cfg.FStarC_TypeChecker_Cfg.reifying);
             FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
               (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
           } in
         let t0 = FStarC_Timing.now_ns () in
         let tm_normed = norm cfg' t_env [] tm in
         maybe_debug cfg tm_normed (FStar_Pervasives_Native.Some (tm, t0));
         rebuild cfg t_env stack2 tm_normed)))
and reduce_impure_comp (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (stack1 : stack_elt Prims.list) (head : FStarC_Syntax_Syntax.term)
  (m :
    (FStarC_Syntax_Syntax.monad_name,
      (FStarC_Syntax_Syntax.monad_name * FStarC_Syntax_Syntax.monad_name))
      FStar_Pervasives.either)
  (t : FStarC_Syntax_Syntax.typ) : FStarC_Syntax_Syntax.term=
  let t1 = norm cfg env1 [] t in
  let metadata =
    match m with
    | FStar_Pervasives.Inl m1 -> FStarC_Syntax_Syntax.Meta_monadic (m1, t1)
    | FStar_Pervasives.Inr (m1, m') ->
        FStarC_Syntax_Syntax.Meta_monadic_lift (m1, m', t1) in
  norm cfg env1 ((Meta (env1, metadata, (head.FStarC_Syntax_Syntax.pos))) ::
    stack1) head
and do_reify_monadic (fallback : unit -> FStarC_Syntax_Syntax.term)
  (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (stack1 : stack_elt Prims.list) (top : FStarC_Syntax_Syntax.term)
  (m : FStarC_Syntax_Syntax.monad_name) (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.term=
  (match stack1 with
   | (App
       (uu___1,
        {
          FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
            (FStarC_Const.Const_reify uu___2);
          FStarC_Syntax_Syntax.pos = uu___3;
          FStarC_Syntax_Syntax.hash_code = uu___4;_},
        uu___5, uu___6))::uu___7
       -> ()
   | uu___1 ->
       let uu___2 =
         let uu___3 =
           FStarC_Class_Show.show
             (FStarC_Class_Show.show_list showable_stack_elt) stack1 in
         FStarC_Format.fmt1 "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
           uu___3 in
       FStarC_Effect.failwith uu___2);
  (let top0 = top in
   let top1 = FStarC_Syntax_Util.unascribe top in
   FStarC_TypeChecker_Cfg.log cfg
     (fun uu___2 ->
        let uu___3 =
          FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term top1 in
        let uu___4 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term top1 in
        FStarC_Format.print2 "Reifying: (%s) %s\n" uu___3 uu___4);
   (let top2 = FStarC_Syntax_Util.unmeta_safe top1 in
    let uu___2 =
      let uu___3 = FStarC_Syntax_Subst.compress top2 in
      uu___3.FStarC_Syntax_Syntax.n in
    match uu___2 with
    | FStarC_Syntax_Syntax.Tm_let
        { FStarC_Syntax_Syntax.lbs = (false, lb::[]);
          FStarC_Syntax_Syntax.body1 = body;_}
        ->
        let eff_name =
          FStarC_TypeChecker_Env.norm_eff_name
            cfg.FStarC_TypeChecker_Cfg.tcenv m in
        let ed =
          FStarC_TypeChecker_Env.get_effect_decl
            cfg.FStarC_TypeChecker_Cfg.tcenv eff_name in
        let uu___3 = FStarC_Option.must (FStarC_Syntax_Util.get_eff_repr ed) in
        (match uu___3 with
         | (uu___4, repr) ->
             let uu___5 =
               FStarC_Option.must (FStarC_Syntax_Util.get_bind_repr ed) in
             (match uu___5 with
              | (uu___6, bind_repr) ->
                  (match lb.FStarC_Syntax_Syntax.lbname with
                   | FStar_Pervasives.Inr uu___7 ->
                       FStarC_Effect.failwith
                         "Cannot reify a top-level let binding"
                   | FStar_Pervasives.Inl x ->
                       let is_return e =
                         let uu___7 =
                           let uu___8 = FStarC_Syntax_Subst.compress e in
                           uu___8.FStarC_Syntax_Syntax.n in
                         match uu___7 with
                         | FStarC_Syntax_Syntax.Tm_meta
                             { FStarC_Syntax_Syntax.tm2 = e1;
                               FStarC_Syntax_Syntax.meta =
                                 FStarC_Syntax_Syntax.Meta_monadic
                                 (uu___8, uu___9);_}
                             ->
                             let uu___10 =
                               let uu___11 = FStarC_Syntax_Subst.compress e1 in
                               uu___11.FStarC_Syntax_Syntax.n in
                             (match uu___10 with
                              | FStarC_Syntax_Syntax.Tm_meta
                                  { FStarC_Syntax_Syntax.tm2 = e2;
                                    FStarC_Syntax_Syntax.meta =
                                      FStarC_Syntax_Syntax.Meta_monadic_lift
                                      (uu___11, msrc, uu___12);_}
                                  when FStarC_Syntax_Util.is_pure_effect msrc
                                  ->
                                  let uu___13 =
                                    FStarC_Syntax_Subst.compress e2 in
                                  FStar_Pervasives_Native.Some uu___13
                              | uu___11 -> FStar_Pervasives_Native.None)
                         | uu___8 -> FStar_Pervasives_Native.None in
                       let uu___7 = is_return lb.FStarC_Syntax_Syntax.lbdef in
                       (match uu___7 with
                        | FStar_Pervasives_Native.Some e ->
                            let lb1 =
                              {
                                FStarC_Syntax_Syntax.lbname =
                                  (lb.FStarC_Syntax_Syntax.lbname);
                                FStarC_Syntax_Syntax.lbunivs =
                                  (lb.FStarC_Syntax_Syntax.lbunivs);
                                FStarC_Syntax_Syntax.lbtyp =
                                  (lb.FStarC_Syntax_Syntax.lbtyp);
                                FStarC_Syntax_Syntax.lbeff =
                                  FStarC_Parser_Const.effect_PURE_lid;
                                FStarC_Syntax_Syntax.lbdef = e;
                                FStarC_Syntax_Syntax.lbattrs =
                                  (lb.FStarC_Syntax_Syntax.lbattrs);
                                FStarC_Syntax_Syntax.lbpos =
                                  (lb.FStarC_Syntax_Syntax.lbpos)
                              } in
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    FStarC_Syntax_Util.mk_reify body
                                      (FStar_Pervasives_Native.Some m) in
                                  {
                                    FStarC_Syntax_Syntax.lbs = (false, [lb1]);
                                    FStarC_Syntax_Syntax.body1 = uu___11
                                  } in
                                FStarC_Syntax_Syntax.Tm_let uu___10 in
                              FStarC_Syntax_Syntax.mk uu___9
                                top2.FStarC_Syntax_Syntax.pos in
                            norm cfg env1 (FStarC_List.tl stack1) uu___8
                        | FStar_Pervasives_Native.None ->
                            let uu___8 =
                              let uu___9 = is_return body in
                              match uu___9 with
                              | FStar_Pervasives_Native.Some
                                  {
                                    FStarC_Syntax_Syntax.n =
                                      FStarC_Syntax_Syntax.Tm_bvar y;
                                    FStarC_Syntax_Syntax.pos = uu___10;
                                    FStarC_Syntax_Syntax.hash_code = uu___11;_}
                                  -> FStarC_Syntax_Syntax.bv_eq x y
                              | uu___10 -> false in
                            if uu___8
                            then
                              norm cfg env1 stack1
                                lb.FStarC_Syntax_Syntax.lbdef
                            else
                              (let rng = top2.FStarC_Syntax_Syntax.pos in
                               let head =
                                 FStarC_Syntax_Util.mk_reify
                                   lb.FStarC_Syntax_Syntax.lbdef
                                   (FStar_Pervasives_Native.Some m) in
                               let body1 =
                                 FStarC_Syntax_Util.mk_reify body
                                   (FStar_Pervasives_Native.Some m) in
                               let body_rc =
                                 {
                                   FStarC_Syntax_Syntax.residual_effect = m;
                                   FStarC_Syntax_Syntax.residual_typ =
                                     (FStar_Pervasives_Native.Some t);
                                   FStarC_Syntax_Syntax.residual_flags = []
                                 } in
                               let body2 =
                                 FStarC_Syntax_Syntax.mk_Tm_abs
                                   [FStarC_Syntax_Syntax.mk_binder x] body1
                                   (FStar_Pervasives_Native.Some body_rc)
                                   body1.FStarC_Syntax_Syntax.pos in
                               let close = closure_as_term cfg env1 in
                               let bind_inst =
                                 let uu___9 =
                                   let uu___10 =
                                     FStarC_Syntax_Subst.compress bind_repr in
                                   uu___10.FStarC_Syntax_Syntax.n in
                                 match uu___9 with
                                 | FStarC_Syntax_Syntax.Tm_uinst
                                     (bind, uu___10::uu___11::[]) ->
                                     let uu___12 =
                                       let uu___13 =
                                         let uu___14 =
                                           let uu___15 =
                                             let uu___16 =
                                               close
                                                 lb.FStarC_Syntax_Syntax.lbtyp in
                                             (cfg.FStarC_TypeChecker_Cfg.tcenv).FStarC_TypeChecker_Env.universe_of
                                               cfg.FStarC_TypeChecker_Cfg.tcenv
                                               uu___16 in
                                           let uu___16 =
                                             let uu___17 =
                                               let uu___18 = close t in
                                               (cfg.FStarC_TypeChecker_Cfg.tcenv).FStarC_TypeChecker_Env.universe_of
                                                 cfg.FStarC_TypeChecker_Cfg.tcenv
                                                 uu___18 in
                                             [uu___17] in
                                           uu___15 :: uu___16 in
                                         (bind, uu___14) in
                                       FStarC_Syntax_Syntax.Tm_uinst uu___13 in
                                     FStarC_Syntax_Syntax.mk uu___12 rng
                                 | uu___10 ->
                                     let uu___11 =
                                       let uu___12 =
                                         FStarC_Class_Show.show
                                           FStarC_Ident.showable_lident
                                           ed.FStarC_Syntax_Syntax.mname in
                                       let uu___13 =
                                         FStarC_Class_Show.show
                                           FStarC_Syntax_Print.showable_term
                                           bind_repr in
                                       FStarC_Format.fmt2
                                         "The bind combinator of effect %s must be polymorphic in exactly two universes (%s)"
                                         uu___12 uu___13 in
                                     FStarC_Errors.raise_error
                                       FStarC_Class_HasRange.hasRange_range
                                       rng
                                       FStarC_Errors_Codes.Fatal_UnexpectedEffect
                                       ()
                                       (Obj.magic
                                          FStarC_Errors_Msg.is_error_message_string)
                                       (Obj.magic uu___11) in
                               let bind_inst_args f_arg =
                                 [FStarC_Syntax_Syntax.as_arg
                                    lb.FStarC_Syntax_Syntax.lbtyp;
                                 FStarC_Syntax_Syntax.as_arg t;
                                 FStarC_Syntax_Syntax.as_arg f_arg;
                                 FStarC_Syntax_Syntax.as_arg body2] in
                               let reified =
                                 let is_total_effect =
                                   FStarC_TypeChecker_Env.is_total_effect
                                     cfg.FStarC_TypeChecker_Cfg.tcenv
                                     eff_name in
                                 if
                                   is_total_effect ||
                                     (FStarC_Ident.lid_equals eff_name
                                        FStarC_Parser_Const.effect_TAC_lid)
                                 then
                                   FStarC_Syntax_Syntax.mk_Tm_app bind_inst
                                     (bind_inst_args head) rng
                                 else
                                   (let uu___9 =
                                      let bv =
                                        FStarC_Syntax_Syntax.new_bv
                                          FStar_Pervasives_Native.None
                                          x.FStarC_Syntax_Syntax.sort in
                                      let lb1 =
                                        let uu___10 =
                                          FStarC_Syntax_Util.mk_app repr
                                            [FStarC_Syntax_Syntax.as_arg
                                               x.FStarC_Syntax_Syntax.sort] in
                                        {
                                          FStarC_Syntax_Syntax.lbname =
                                            (FStar_Pervasives.Inl bv);
                                          FStarC_Syntax_Syntax.lbunivs = [];
                                          FStarC_Syntax_Syntax.lbtyp =
                                            uu___10;
                                          FStarC_Syntax_Syntax.lbeff =
                                            (if is_total_effect
                                             then
                                               FStarC_Parser_Const.effect_Tot_lid
                                             else
                                               FStarC_Parser_Const.effect_Dv_lid);
                                          FStarC_Syntax_Syntax.lbdef = head;
                                          FStarC_Syntax_Syntax.lbattrs = [];
                                          FStarC_Syntax_Syntax.lbpos =
                                            (head.FStarC_Syntax_Syntax.pos)
                                        } in
                                      let uu___10 =
                                        FStarC_Syntax_Syntax.bv_to_name bv in
                                      (lb1, bv, uu___10) in
                                    match uu___9 with
                                    | (lb_head, head_bv, head1) ->
                                        let uu___10 =
                                          let uu___11 =
                                            let uu___12 =
                                              let uu___13 =
                                                FStarC_Syntax_Syntax.mk_Tm_app
                                                  bind_inst
                                                  (bind_inst_args head1) rng in
                                              FStarC_Syntax_Subst.close
                                                [FStarC_Syntax_Syntax.mk_binder
                                                   head_bv] uu___13 in
                                            {
                                              FStarC_Syntax_Syntax.lbs =
                                                (false, [lb_head]);
                                              FStarC_Syntax_Syntax.body1 =
                                                uu___12
                                            } in
                                          FStarC_Syntax_Syntax.Tm_let uu___11 in
                                        FStarC_Syntax_Syntax.mk uu___10 rng) in
                               FStarC_TypeChecker_Cfg.log cfg
                                 (fun uu___10 ->
                                    let uu___11 =
                                      FStarC_Class_Show.show
                                        FStarC_Syntax_Print.showable_term
                                        top0 in
                                    let uu___12 =
                                      FStarC_Class_Show.show
                                        FStarC_Syntax_Print.showable_term
                                        reified in
                                    FStarC_Format.print2
                                      "Reified (1) <%s> to %s\n" uu___11
                                      uu___12);
                               norm cfg env1 (FStarC_List.tl stack1) reified)))))
    | FStarC_Syntax_Syntax.Tm_let
        { FStarC_Syntax_Syntax.lbs = (true, lbs);
          FStarC_Syntax_Syntax.body1 = body;_}
        ->
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                FStarC_Syntax_Util.mk_reify body
                  (FStar_Pervasives_Native.Some m) in
              {
                FStarC_Syntax_Syntax.lbs = (true, lbs);
                FStarC_Syntax_Syntax.body1 = uu___6
              } in
            FStarC_Syntax_Syntax.Tm_let uu___5 in
          FStarC_Syntax_Syntax.mk uu___4 top2.FStarC_Syntax_Syntax.pos in
        norm cfg env1 (FStarC_List.tl stack1) uu___3
    | FStarC_Syntax_Syntax.Tm_app uu___3 ->
        (FStarC_TypeChecker_Cfg.log cfg
           (fun uu___5 ->
              let uu___6 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term top0 in
              FStarC_Format.print1 "Reified (2) <%s>\n" uu___6);
         (let uu___5 =
            FStarC_Syntax_Util.mk_reify top2 (FStar_Pervasives_Native.Some m) in
          norm cfg env1 (FStarC_List.tl stack1) uu___5))
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = e;
          FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic
            uu___3;_}
        -> do_reify_monadic fallback cfg env1 stack1 e m t
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = e;
          FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic_lift
            (msrc, mtgt, t');_}
        ->
        let lifted =
          let uu___3 = closure_as_term cfg env1 t' in
          reify_lift cfg e msrc mtgt uu___3 in
        (FStarC_TypeChecker_Cfg.log cfg
           (fun uu___4 ->
              let uu___5 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                  lifted in
              FStarC_Format.print1 "Reified lift to (2): %s\n" uu___5);
         norm cfg env1 (FStarC_List.tl stack1) lifted)
    | FStarC_Syntax_Syntax.Tm_match
        { FStarC_Syntax_Syntax.scrutinee = e;
          FStarC_Syntax_Syntax.ret_opt = asc_opt;
          FStarC_Syntax_Syntax.brs = branches1;
          FStarC_Syntax_Syntax.rc_opt1 = lopt;_}
        ->
        let branches2 =
          FStarC_List.map
            (fun uu___3 ->
               match uu___3 with
               | (pat, wopt, tm) ->
                   let uu___4 =
                     FStarC_Syntax_Util.mk_reify tm
                       (FStar_Pervasives_Native.Some m) in
                   (pat, wopt, uu___4)) branches1 in
        let tm =
          FStarC_Syntax_Syntax.mk
            (FStarC_Syntax_Syntax.Tm_match
               {
                 FStarC_Syntax_Syntax.scrutinee = e;
                 FStarC_Syntax_Syntax.ret_opt = asc_opt;
                 FStarC_Syntax_Syntax.brs = branches2;
                 FStarC_Syntax_Syntax.rc_opt1 = lopt
               }) top2.FStarC_Syntax_Syntax.pos in
        norm cfg env1 (FStarC_List.tl stack1) tm
    | uu___3 -> fallback ()))
and reify_lift (cfg : FStarC_TypeChecker_Cfg.cfg)
  (e : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  (msrc : FStarC_Syntax_Syntax.monad_name)
  (mtgt : FStarC_Syntax_Syntax.monad_name) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  let env1 = cfg.FStarC_TypeChecker_Cfg.tcenv in
  FStarC_TypeChecker_Cfg.log cfg
    (fun uu___1 ->
       let uu___2 =
         FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
       FStarC_Format.print3 "Reifying lift %s -> %s: %s\n"
         (FStarC_Ident.string_of_lid msrc) (FStarC_Ident.string_of_lid mtgt)
         uu___2);
  (let uu___1 =
     let uu___2 = FStarC_TypeChecker_Env.norm_eff_name env1 msrc in
     let uu___3 = FStarC_TypeChecker_Env.norm_eff_name env1 mtgt in
     FStarC_TypeChecker_Env.lookup_lift env1 uu___2 uu___3 in
   match uu___1 with
   | FStar_Pervasives_Native.Some (uu___2, lift) ->
       let lift1 =
         let uu___3 =
           let uu___4 = FStarC_Syntax_Subst.compress lift in
           uu___4.FStarC_Syntax_Syntax.n in
         match uu___3 with
         | FStarC_Syntax_Syntax.Tm_uinst (lift_tm, uu___4::[]) ->
             let uu___5 =
               let uu___6 =
                 let uu___7 =
                   let uu___8 =
                     env1.FStarC_TypeChecker_Env.universe_of env1 t in
                   [uu___8] in
                 (lift_tm, uu___7) in
               FStarC_Syntax_Syntax.Tm_uinst uu___6 in
             FStarC_Syntax_Syntax.mk uu___5 e.FStarC_Syntax_Syntax.pos
         | uu___4 -> lift in
       let e1 =
         let uu___3 = FStarC_TypeChecker_Env.is_reifiable_effect env1 msrc in
         if uu___3
         then
           FStarC_Syntax_Util.mk_reify e (FStar_Pervasives_Native.Some msrc)
         else
           (let uu___4 =
              let uu___5 =
                let uu___6 =
                  FStarC_Syntax_Syntax.null_binder
                    FStarC_Syntax_Syntax.t_unit in
                {
                  FStarC_Syntax_Syntax.b = uu___6;
                  FStarC_Syntax_Syntax.body = e;
                  FStarC_Syntax_Syntax.rc_opt =
                    (FStar_Pervasives_Native.Some
                       {
                         FStarC_Syntax_Syntax.residual_effect = msrc;
                         FStarC_Syntax_Syntax.residual_typ =
                           (FStar_Pervasives_Native.Some t);
                         FStarC_Syntax_Syntax.residual_flags = []
                       })
                } in
              FStarC_Syntax_Syntax.Tm_abs uu___5 in
            FStarC_Syntax_Syntax.mk uu___4 e.FStarC_Syntax_Syntax.pos) in
       FStarC_Syntax_Syntax.mk_Tm_app lift1
         [FStarC_Syntax_Syntax.as_arg t; FStarC_Syntax_Syntax.as_arg e1]
         e1.FStarC_Syntax_Syntax.pos
   | FStar_Pervasives_Native.None ->
       (if
          Prims.not
            (((FStarC_Syntax_Util.is_pure_effect msrc) ||
                (FStarC_Syntax_Util.is_div_effect msrc))
               || (FStarC_Syntax_Util.is_ghost_effect msrc))
        then
          FStarC_Effect.failwith
            (FStarC_Format.fmt2
               "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               (FStarC_Ident.string_of_lid msrc)
               (FStarC_Ident.string_of_lid mtgt))
        else ();
        (let ed =
           let uu___3 = FStarC_TypeChecker_Env.norm_eff_name env1 mtgt in
           FStarC_TypeChecker_Env.get_effect_decl env1 uu___3 in
         let uu___3 = FStarC_Option.must (FStarC_Syntax_Util.get_eff_repr ed) in
         match uu___3 with
         | (uu___4, repr) ->
             let uu___5 =
               FStarC_Option.must (FStarC_Syntax_Util.get_return_repr ed) in
             (match uu___5 with
              | (uu___6, return_repr) ->
                  let return_inst =
                    let uu___7 =
                      let uu___8 = FStarC_Syntax_Subst.compress return_repr in
                      uu___8.FStarC_Syntax_Syntax.n in
                    match uu___7 with
                    | FStarC_Syntax_Syntax.Tm_uinst (return_tm, uu___8::[])
                        ->
                        let uu___9 =
                          let uu___10 =
                            let uu___11 =
                              let uu___12 =
                                env1.FStarC_TypeChecker_Env.universe_of env1
                                  t in
                              [uu___12] in
                            (return_tm, uu___11) in
                          FStarC_Syntax_Syntax.Tm_uinst uu___10 in
                        FStarC_Syntax_Syntax.mk uu___9
                          e.FStarC_Syntax_Syntax.pos
                    | uu___8 ->
                        let uu___9 =
                          let uu___10 =
                            FStarC_Class_Show.show
                              FStarC_Ident.showable_lident
                              ed.FStarC_Syntax_Syntax.mname in
                          let uu___11 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term return_repr in
                          FStarC_Format.fmt2
                            "The return combinator of effect %s must be polymorphic in exactly one universe (%s)"
                            uu___10 uu___11 in
                        FStarC_Errors.raise_error
                          FStarC_Class_HasRange.hasRange_range
                          e.FStarC_Syntax_Syntax.pos
                          FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                          (Obj.magic
                             FStarC_Errors_Msg.is_error_message_string)
                          (Obj.magic uu___9) in
                  let uu___7 =
                    let bv =
                      FStarC_Syntax_Syntax.new_bv
                        FStar_Pervasives_Native.None t in
                    let lb =
                      let uu___8 =
                        FStarC_Syntax_Util.mk_app repr
                          [FStarC_Syntax_Syntax.as_arg t] in
                      {
                        FStarC_Syntax_Syntax.lbname =
                          (FStar_Pervasives.Inl bv);
                        FStarC_Syntax_Syntax.lbunivs = [];
                        FStarC_Syntax_Syntax.lbtyp = uu___8;
                        FStarC_Syntax_Syntax.lbeff = msrc;
                        FStarC_Syntax_Syntax.lbdef = e;
                        FStarC_Syntax_Syntax.lbattrs = [];
                        FStarC_Syntax_Syntax.lbpos =
                          (e.FStarC_Syntax_Syntax.pos)
                      } in
                    let uu___8 = FStarC_Syntax_Syntax.bv_to_name bv in
                    (lb, bv, uu___8) in
                  (match uu___7 with
                   | (lb_e, e_bv, e1) ->
                       let uu___8 =
                         let uu___9 =
                           let uu___10 =
                             let uu___11 =
                               FStarC_Syntax_Syntax.mk_Tm_app return_inst
                                 [FStarC_Syntax_Syntax.as_arg t;
                                 FStarC_Syntax_Syntax.as_arg e1]
                                 e1.FStarC_Syntax_Syntax.pos in
                             FStarC_Syntax_Subst.close
                               [FStarC_Syntax_Syntax.mk_binder e_bv] uu___11 in
                           {
                             FStarC_Syntax_Syntax.lbs = (false, [lb_e]);
                             FStarC_Syntax_Syntax.body1 = uu___10
                           } in
                         FStarC_Syntax_Syntax.Tm_let uu___9 in
                       FStarC_Syntax_Syntax.mk uu___8
                         e1.FStarC_Syntax_Syntax.pos)))))
and norm_pattern_args (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (args :
    (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
      FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list Prims.list)
  : FStarC_Syntax_Syntax.arg Prims.list Prims.list=
  FStarC_List.map
    (FStarC_List.map
       (fun uu___ ->
          match uu___ with
          | (a, imp) -> let uu___1 = norm cfg env1 [] a in (uu___1, imp)))
    args
and norm_comp (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (comp : FStarC_Syntax_Syntax.comp) : FStarC_Syntax_Syntax.comp=
  FStarC_TypeChecker_Cfg.log cfg
    (fun uu___1 ->
       let uu___2 =
         FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp comp in
       let uu___3 =
         FStarC_Class_Show.show FStarC_Class_Show.showable_nat
           (FStarC_List.length env1) in
       FStarC_Format.print2 ">>> %s\nNormComp with with %s env elements\n"
         uu___2 uu___3);
  (match comp.FStarC_Syntax_Syntax.n with
   | FStarC_Syntax_Syntax.Total t ->
       let t1 = norm cfg env1 [] t in
       let uu___1 = FStarC_Syntax_Syntax.mk_Total t1 in
       {
         FStarC_Syntax_Syntax.n = (uu___1.FStarC_Syntax_Syntax.n);
         FStarC_Syntax_Syntax.pos = (comp.FStarC_Syntax_Syntax.pos);
         FStarC_Syntax_Syntax.hash_code =
           (uu___1.FStarC_Syntax_Syntax.hash_code)
       }
   | FStarC_Syntax_Syntax.GTotal t ->
       let t1 = norm cfg env1 [] t in
       let uu___1 = FStarC_Syntax_Syntax.mk_GTotal t1 in
       {
         FStarC_Syntax_Syntax.n = (uu___1.FStarC_Syntax_Syntax.n);
         FStarC_Syntax_Syntax.pos = (comp.FStarC_Syntax_Syntax.pos);
         FStarC_Syntax_Syntax.hash_code =
           (uu___1.FStarC_Syntax_Syntax.hash_code)
       }
   | FStarC_Syntax_Syntax.Comp ct ->
       let uu___1 =
         if
           (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
         then
           let uu___2 =
             FStarC_Syntax_Syntax.trivial_post
               ct.FStarC_Syntax_Syntax.result_typ in
           (FStarC_Syntax_Syntax.trivial_pre, uu___2)
         else
           (let uu___2 = norm cfg env1 [] ct.FStarC_Syntax_Syntax.comp_pre in
            let uu___3 = norm cfg env1 [] ct.FStarC_Syntax_Syntax.comp_post in
            (uu___2, uu___3)) in
       (match uu___1 with
        | (comp_pre, comp_post) ->
            let flags =
              FStarC_List.map
                (fun uu___2 ->
                   match uu___2 with
                   | FStarC_Syntax_Syntax.DECREASES
                       (FStarC_Syntax_Syntax.Decreases_lex l) ->
                       let uu___3 =
                         let uu___4 = FStarC_List.map (norm cfg env1 []) l in
                         FStarC_Syntax_Syntax.Decreases_lex uu___4 in
                       FStarC_Syntax_Syntax.DECREASES uu___3
                   | FStarC_Syntax_Syntax.DECREASES
                       (FStarC_Syntax_Syntax.Decreases_wf (rel, e)) ->
                       let uu___3 =
                         let uu___4 =
                           let uu___5 = norm cfg env1 [] rel in
                           let uu___6 = norm cfg env1 [] e in
                           (uu___5, uu___6) in
                         FStarC_Syntax_Syntax.Decreases_wf uu___4 in
                       FStarC_Syntax_Syntax.DECREASES uu___3
                   | f -> f) ct.FStarC_Syntax_Syntax.flags in
            let comp_univs =
              FStarC_List.map (norm_universe cfg env1)
                ct.FStarC_Syntax_Syntax.comp_univs in
            let result_typ =
              norm cfg env1 [] ct.FStarC_Syntax_Syntax.result_typ in
            let uu___2 =
              FStarC_Syntax_Syntax.mk_Comp
                {
                  FStarC_Syntax_Syntax.comp_univs = comp_univs;
                  FStarC_Syntax_Syntax.effect_name =
                    (ct.FStarC_Syntax_Syntax.effect_name);
                  FStarC_Syntax_Syntax.result_typ = result_typ;
                  FStarC_Syntax_Syntax.comp_pre = comp_pre;
                  FStarC_Syntax_Syntax.comp_post = comp_post;
                  FStarC_Syntax_Syntax.flags = flags
                } in
            {
              FStarC_Syntax_Syntax.n = (uu___2.FStarC_Syntax_Syntax.n);
              FStarC_Syntax_Syntax.pos = (comp.FStarC_Syntax_Syntax.pos);
              FStarC_Syntax_Syntax.hash_code =
                (uu___2.FStarC_Syntax_Syntax.hash_code)
            }))
and norm_binder (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (b : FStarC_Syntax_Syntax.binder) : FStarC_Syntax_Syntax.binder=
  let x =
    let uu___ = b.FStarC_Syntax_Syntax.binder_bv in
    let uu___1 =
      norm cfg env1 []
        (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
    {
      FStarC_Syntax_Syntax.ppname = (uu___.FStarC_Syntax_Syntax.ppname);
      FStarC_Syntax_Syntax.index = (uu___.FStarC_Syntax_Syntax.index);
      FStarC_Syntax_Syntax.sort = uu___1
    } in
  let imp =
    match b.FStarC_Syntax_Syntax.binder_qual with
    | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t) ->
        let uu___ =
          let uu___1 = closure_as_term cfg env1 t in
          FStarC_Syntax_Syntax.Meta uu___1 in
        FStar_Pervasives_Native.Some uu___
    | i -> i in
  let attrs =
    FStarC_List.map (norm cfg env1 []) b.FStarC_Syntax_Syntax.binder_attrs in
  FStarC_Syntax_Syntax.mk_binder_with_attrs x imp
    b.FStarC_Syntax_Syntax.binder_positivity attrs
and norm_binders (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (bs : FStarC_Syntax_Syntax.binders) : FStarC_Syntax_Syntax.binders=
  let uu___ =
    FStarC_List.fold_left
      (fun uu___1 b ->
         match uu___1 with
         | (nbs', env2) ->
             let b1 = norm_binder cfg env2 b in
             let uu___2 = let uu___3 = dummy () in uu___3 :: env2 in
             ((b1 :: nbs'), uu___2)) ([], env1) bs in
  match uu___ with | (nbs, uu___1) -> FStarC_List.rev nbs
and maybe_simplify (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (stack1 : stack) (tm : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.term * Prims.bool)=
  let uu___ = maybe_simplify_aux cfg env1 stack1 tm in
  match uu___ with
  | (tm', renorm) ->
      (if (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.b380
       then
         (let uu___2 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tm in
          let uu___3 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tm' in
          let uu___4 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_bool renorm in
          FStarC_Format.print4 "%sSimplified\n\t%s to\n\t%s\nrenorm = %s\n"
            (if
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.simplify
             then ""
             else "NOT ") uu___2 uu___3 uu___4)
       else ();
       (tm', renorm))
and norm_cb (cfg : FStarC_TypeChecker_Cfg.cfg) :
  FStarC_Syntax_Embeddings_Base.norm_cb=
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives.Inr x -> norm cfg [] [] x
    | FStar_Pervasives.Inl l ->
        let uu___1 =
          FStarC_Syntax_DsEnv.try_lookup_lid
            (cfg.FStarC_TypeChecker_Cfg.tcenv).FStarC_TypeChecker_Env.dsenv l in
        (match uu___1 with
         | FStar_Pervasives_Native.Some t -> t
         | FStar_Pervasives_Native.None ->
             FStarC_Syntax_Syntax.fv_to_tm
               (FStarC_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None))
and maybe_simplify_aux (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (stack1 : stack) (tm : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.term * Prims.bool)=
  let uu___ = reduce_primops (norm_cb cfg) cfg env1 tm in
  match uu___ with
  | (tm1, renorm) ->
      if
        Prims.not
          (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.simplify
      then (tm1, renorm)
      else
        (let w t =
           {
             FStarC_Syntax_Syntax.n = (t.FStarC_Syntax_Syntax.n);
             FStarC_Syntax_Syntax.pos = (tm1.FStarC_Syntax_Syntax.pos);
             FStarC_Syntax_Syntax.hash_code =
               (t.FStarC_Syntax_Syntax.hash_code)
           } in
         let simp_t t =
           let uu___1 =
             let uu___2 = FStarC_Syntax_Util.unmeta t in
             uu___2.FStarC_Syntax_Syntax.n in
           match uu___1 with
           | FStarC_Syntax_Syntax.Tm_fvar fv when
               FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.true_lid
               -> FStar_Pervasives_Native.Some true
           | FStarC_Syntax_Syntax.Tm_fvar fv when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Parser_Const.false_lid
               -> FStar_Pervasives_Native.Some false
           | uu___2 -> FStar_Pervasives_Native.None in
         let is_const_match phi =
           let uu___1 =
             let uu___2 = FStarC_Syntax_Subst.compress phi in
             uu___2.FStarC_Syntax_Syntax.n in
           match uu___1 with
           | FStarC_Syntax_Syntax.Tm_match
               { FStarC_Syntax_Syntax.scrutinee = uu___2;
                 FStarC_Syntax_Syntax.ret_opt = uu___3;
                 FStarC_Syntax_Syntax.brs = br::brs;
                 FStarC_Syntax_Syntax.rc_opt1 = uu___4;_}
               ->
               let uu___5 = br in
               (match uu___5 with
                | (uu___6, uu___7, e) ->
                    let r =
                      let uu___8 = simp_t e in
                      match uu___8 with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some b ->
                          let uu___9 =
                            FStarC_List.for_all
                              (fun uu___10 ->
                                 match uu___10 with
                                 | (uu___11, uu___12, e') ->
                                     let uu___13 = simp_t e' in
                                     uu___13 =
                                       (FStar_Pervasives_Native.Some b)) brs in
                          if uu___9
                          then FStar_Pervasives_Native.Some b
                          else FStar_Pervasives_Native.None in
                    r)
           | uu___2 -> FStar_Pervasives_Native.None in
         let rec clearly_inhabited ty =
           let uu___1 =
             let uu___2 = FStarC_Syntax_Util.unmeta ty in
             uu___2.FStarC_Syntax_Syntax.n in
           match uu___1 with
           | FStarC_Syntax_Syntax.Tm_uinst (t, uu___2) -> clearly_inhabited t
           | FStarC_Syntax_Syntax.Tm_arrow
               { FStarC_Syntax_Syntax.b1 = uu___2;
                 FStarC_Syntax_Syntax.comp = c;_}
               -> clearly_inhabited (FStarC_Syntax_Util.comp_result c)
           | FStarC_Syntax_Syntax.Tm_fvar fv ->
               let l = FStarC_Syntax_Syntax.lid_of_fv fv in
               (((FStarC_Ident.lid_equals l FStarC_Parser_Const.int_lid) ||
                   (FStarC_Ident.lid_equals l FStarC_Parser_Const.bool_lid))
                  ||
                  (FStarC_Ident.lid_equals l FStarC_Parser_Const.string_lid))
                 || (FStarC_Ident.lid_equals l FStarC_Parser_Const.exn_lid)
           | uu___2 -> false in
         let simplify arg =
           let uu___1 = simp_t (FStar_Pervasives_Native.fst arg) in
           (uu___1, arg) in
         let uu___1 = is_forall_const cfg tm1 in
         match uu___1 with
         | FStar_Pervasives_Native.Some tm' ->
             (if
                (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
              then
                (let uu___3 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     tm1 in
                 let uu___4 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     tm' in
                 FStarC_Format.print2 "WPE> %s ~> %s\n" uu___3 uu___4)
              else ();
              (let uu___3 = norm cfg env1 [] tm' in
               maybe_simplify_aux cfg env1 stack1 uu___3))
         | FStar_Pervasives_Native.None ->
             let uu___2 = is_one_point cfg tm1 in
             (match uu___2 with
              | FStar_Pervasives_Native.Some tm' ->
                  let uu___3 = norm cfg env1 [] tm' in
                  maybe_simplify_aux cfg env1 stack1 uu___3
              | FStar_Pervasives_Native.None ->
                  let uu___3 =
                    let uu___4 = FStarC_Syntax_Subst.compress tm1 in
                    uu___4.FStarC_Syntax_Syntax.n in
                  (match uu___3 with
                   | FStarC_Syntax_Syntax.Tm_app uu___4 ->
                       let uu___5 = FStarC_Syntax_Util.head_and_args_full tm1 in
                       (match uu___5 with
                        | (hd, args) ->
                            let uu___6 =
                              let uu___7 = FStarC_Syntax_Util.un_uinst hd in
                              uu___7.FStarC_Syntax_Syntax.n in
                            (match uu___6 with
                             | FStarC_Syntax_Syntax.Tm_fvar fv ->
                                 if
                                   FStarC_Syntax_Syntax.fv_eq_lid fv
                                     FStarC_Parser_Const.and_lid
                                 then
                                   let uu___7 = FStarC_List.map simplify args in
                                   (match uu___7 with
                                    | (FStar_Pervasives_Native.Some true,
                                       uu___8)::(uu___9, (arg, uu___10))::[]
                                        -> (arg, false)
                                    | (uu___8, (arg, uu___9))::(FStar_Pervasives_Native.Some
                                                                true,
                                                                uu___10)::[]
                                        -> (arg, false)
                                    | (FStar_Pervasives_Native.Some false,
                                       uu___8)::uu___9::[] ->
                                        ((w FStarC_Syntax_Util.t_false),
                                          false)
                                    | uu___8::(FStar_Pervasives_Native.Some
                                               false, uu___9)::[]
                                        ->
                                        ((w FStarC_Syntax_Util.t_false),
                                          false)
                                    | uu___8 -> (tm1, false))
                                 else
                                   if
                                     FStarC_Syntax_Syntax.fv_eq_lid fv
                                       FStarC_Parser_Const.or_lid
                                   then
                                     (let uu___7 =
                                        FStarC_List.map simplify args in
                                      match uu___7 with
                                      | (FStar_Pervasives_Native.Some true,
                                         uu___8)::uu___9::[] ->
                                          ((w FStarC_Syntax_Util.t_true),
                                            false)
                                      | uu___8::(FStar_Pervasives_Native.Some
                                                 true, uu___9)::[]
                                          ->
                                          ((w FStarC_Syntax_Util.t_true),
                                            false)
                                      | (FStar_Pervasives_Native.Some false,
                                         uu___8)::(uu___9, (arg, uu___10))::[]
                                          -> (arg, false)
                                      | (uu___8, (arg, uu___9))::(FStar_Pervasives_Native.Some
                                                                  false,
                                                                  uu___10)::[]
                                          -> (arg, false)
                                      | uu___8 -> (tm1, false))
                                   else
                                     if
                                       FStarC_Syntax_Syntax.fv_eq_lid fv
                                         FStarC_Parser_Const.imp_lid
                                     then
                                       (let uu___7 =
                                          FStarC_List.map simplify args in
                                        match uu___7 with
                                        | uu___8::(FStar_Pervasives_Native.Some
                                                   true, uu___9)::[]
                                            ->
                                            ((w FStarC_Syntax_Util.t_true),
                                              false)
                                        | (FStar_Pervasives_Native.Some
                                           false, uu___8)::uu___9::[] ->
                                            ((w FStarC_Syntax_Util.t_true),
                                              false)
                                        | (FStar_Pervasives_Native.Some true,
                                           uu___8)::(uu___9, (arg, uu___10))::[]
                                            -> (arg, false)
                                        | (uu___8, (p, uu___9))::(uu___10,
                                                                  (q,
                                                                   uu___11))::[]
                                            ->
                                            let uu___12 =
                                              FStarC_Syntax_Util.term_eq p q in
                                            if uu___12
                                            then
                                              ((w FStarC_Syntax_Util.t_true),
                                                false)
                                            else (tm1, false)
                                        | uu___8 -> (tm1, false))
                                     else
                                       if
                                         FStarC_Syntax_Syntax.fv_eq_lid fv
                                           FStarC_Parser_Const.iff_lid
                                       then
                                         (let uu___7 =
                                            FStarC_List.map simplify args in
                                          match uu___7 with
                                          | (FStar_Pervasives_Native.Some
                                             true, uu___8)::(FStar_Pervasives_Native.Some
                                                             true, uu___9)::[]
                                              ->
                                              ((w FStarC_Syntax_Util.t_true),
                                                false)
                                          | (FStar_Pervasives_Native.Some
                                             false, uu___8)::(FStar_Pervasives_Native.Some
                                                              false, uu___9)::[]
                                              ->
                                              ((w FStarC_Syntax_Util.t_true),
                                                false)
                                          | (FStar_Pervasives_Native.Some
                                             true, uu___8)::(FStar_Pervasives_Native.Some
                                                             false, uu___9)::[]
                                              ->
                                              ((w FStarC_Syntax_Util.t_false),
                                                false)
                                          | (FStar_Pervasives_Native.Some
                                             false, uu___8)::(FStar_Pervasives_Native.Some
                                                              true, uu___9)::[]
                                              ->
                                              ((w FStarC_Syntax_Util.t_false),
                                                false)
                                          | (uu___8, (arg, uu___9))::
                                              (FStar_Pervasives_Native.Some
                                               true, uu___10)::[]
                                              -> (arg, false)
                                          | (FStar_Pervasives_Native.Some
                                             true, uu___8)::(uu___9,
                                                             (arg, uu___10))::[]
                                              -> (arg, false)
                                          | (uu___8, (arg, uu___9))::
                                              (FStar_Pervasives_Native.Some
                                               false, uu___10)::[]
                                              ->
                                              let uu___11 =
                                                FStarC_Syntax_Util.mk_neg arg in
                                              (uu___11, false)
                                          | (FStar_Pervasives_Native.Some
                                             false, uu___8)::(uu___9,
                                                              (arg, uu___10))::[]
                                              ->
                                              let uu___11 =
                                                FStarC_Syntax_Util.mk_neg arg in
                                              (uu___11, false)
                                          | (uu___8, (p, uu___9))::(uu___10,
                                                                    (q,
                                                                    uu___11))::[]
                                              ->
                                              let uu___12 =
                                                FStarC_Syntax_Util.term_eq p
                                                  q in
                                              if uu___12
                                              then
                                                ((w FStarC_Syntax_Util.t_true),
                                                  false)
                                              else (tm1, false)
                                          | uu___8 -> (tm1, false))
                                       else
                                         if
                                           FStarC_Syntax_Syntax.fv_eq_lid fv
                                             FStarC_Parser_Const.not_lid
                                         then
                                           (let uu___7 =
                                              FStarC_List.map simplify args in
                                            match uu___7 with
                                            | (FStar_Pervasives_Native.Some
                                               true, uu___8)::[] ->
                                                ((w
                                                    FStarC_Syntax_Util.t_false),
                                                  false)
                                            | (FStar_Pervasives_Native.Some
                                               false, uu___8)::[] ->
                                                ((w FStarC_Syntax_Util.t_true),
                                                  false)
                                            | uu___8 -> (tm1, false))
                                         else
                                           if
                                             FStarC_Syntax_Syntax.fv_eq_lid
                                               fv
                                               FStarC_Parser_Const.forall_lid
                                           then
                                             (match args with
                                              | (t, uu___7)::[] ->
                                                  let uu___8 =
                                                    let uu___9 =
                                                      FStarC_Syntax_Subst.compress
                                                        t in
                                                    uu___9.FStarC_Syntax_Syntax.n in
                                                  (match uu___8 with
                                                   | FStarC_Syntax_Syntax.Tm_abs
                                                       {
                                                         FStarC_Syntax_Syntax.b
                                                           = uu___9;
                                                         FStarC_Syntax_Syntax.body
                                                           = body;
                                                         FStarC_Syntax_Syntax.rc_opt
                                                           = uu___10;_}
                                                       ->
                                                       let uu___11 =
                                                         simp_t body in
                                                       (match uu___11 with
                                                        | FStar_Pervasives_Native.Some
                                                            true ->
                                                            ((w
                                                                FStarC_Syntax_Util.t_true),
                                                              false)
                                                        | uu___12 ->
                                                            (tm1, false))
                                                   | uu___9 -> (tm1, false))
                                              | (ty,
                                                 FStar_Pervasives_Native.Some
                                                 {
                                                   FStarC_Syntax_Syntax.aqual_implicit
                                                     = true;
                                                   FStarC_Syntax_Syntax.aqual_attributes
                                                     = uu___7;_})::(t,
                                                                    uu___8)::[]
                                                  ->
                                                  let uu___9 =
                                                    let uu___10 =
                                                      FStarC_Syntax_Subst.compress
                                                        t in
                                                    uu___10.FStarC_Syntax_Syntax.n in
                                                  (match uu___9 with
                                                   | FStarC_Syntax_Syntax.Tm_abs
                                                       {
                                                         FStarC_Syntax_Syntax.b
                                                           = uu___10;
                                                         FStarC_Syntax_Syntax.body
                                                           = body;
                                                         FStarC_Syntax_Syntax.rc_opt
                                                           = uu___11;_}
                                                       ->
                                                       let uu___12 =
                                                         simp_t body in
                                                       (match uu___12 with
                                                        | FStar_Pervasives_Native.Some
                                                            true ->
                                                            ((w
                                                                FStarC_Syntax_Util.t_true),
                                                              false)
                                                        | FStar_Pervasives_Native.Some
                                                            false when
                                                            clearly_inhabited
                                                              ty
                                                            ->
                                                            ((w
                                                                FStarC_Syntax_Util.t_false),
                                                              false)
                                                        | uu___13 ->
                                                            (tm1, false))
                                                   | uu___10 -> (tm1, false))
                                              | uu___7 -> (tm1, false))
                                           else
                                             if
                                               FStarC_Syntax_Syntax.fv_eq_lid
                                                 fv
                                                 FStarC_Parser_Const.exists_lid
                                             then
                                               (match args with
                                                | (t, uu___7)::[] ->
                                                    let uu___8 =
                                                      let uu___9 =
                                                        FStarC_Syntax_Subst.compress
                                                          t in
                                                      uu___9.FStarC_Syntax_Syntax.n in
                                                    (match uu___8 with
                                                     | FStarC_Syntax_Syntax.Tm_abs
                                                         {
                                                           FStarC_Syntax_Syntax.b
                                                             = uu___9;
                                                           FStarC_Syntax_Syntax.body
                                                             = body;
                                                           FStarC_Syntax_Syntax.rc_opt
                                                             = uu___10;_}
                                                         ->
                                                         let uu___11 =
                                                           simp_t body in
                                                         (match uu___11 with
                                                          | FStar_Pervasives_Native.Some
                                                              false ->
                                                              ((w
                                                                  FStarC_Syntax_Util.t_false),
                                                                false)
                                                          | uu___12 ->
                                                              (tm1, false))
                                                     | uu___9 -> (tm1, false))
                                                | (ty,
                                                   FStar_Pervasives_Native.Some
                                                   {
                                                     FStarC_Syntax_Syntax.aqual_implicit
                                                       = true;
                                                     FStarC_Syntax_Syntax.aqual_attributes
                                                       = uu___7;_})::
                                                    (t, uu___8)::[] ->
                                                    let uu___9 =
                                                      let uu___10 =
                                                        FStarC_Syntax_Subst.compress
                                                          t in
                                                      uu___10.FStarC_Syntax_Syntax.n in
                                                    (match uu___9 with
                                                     | FStarC_Syntax_Syntax.Tm_abs
                                                         {
                                                           FStarC_Syntax_Syntax.b
                                                             = uu___10;
                                                           FStarC_Syntax_Syntax.body
                                                             = body;
                                                           FStarC_Syntax_Syntax.rc_opt
                                                             = uu___11;_}
                                                         ->
                                                         let uu___12 =
                                                           simp_t body in
                                                         (match uu___12 with
                                                          | FStar_Pervasives_Native.Some
                                                              false ->
                                                              ((w
                                                                  FStarC_Syntax_Util.t_false),
                                                                false)
                                                          | FStar_Pervasives_Native.Some
                                                              true when
                                                              clearly_inhabited
                                                                ty
                                                              ->
                                                              ((w
                                                                  FStarC_Syntax_Util.t_true),
                                                                false)
                                                          | uu___13 ->
                                                              (tm1, false))
                                                     | uu___10 ->
                                                         (tm1, false))
                                                | uu___7 -> (tm1, false))
                                             else
                                               if
                                                 FStarC_Syntax_Syntax.fv_eq_lid
                                                   fv
                                                   FStarC_Parser_Const.nonempty_lid
                                               then
                                                 (match args with
                                                  | (ty, uu___7)::[] when
                                                      clearly_inhabited ty ->
                                                      ((w
                                                          FStarC_Syntax_Util.t_true),
                                                        false)
                                                  | uu___7 -> (tm1, false))
                                               else
                                                 if
                                                   FStarC_Syntax_Syntax.fv_eq_lid
                                                     fv
                                                     FStarC_Parser_Const.b2t_lid
                                                 then
                                                   (match args with
                                                    | ({
                                                         FStarC_Syntax_Syntax.n
                                                           =
                                                           FStarC_Syntax_Syntax.Tm_constant
                                                           (FStarC_Const.Const_bool
                                                           true);
                                                         FStarC_Syntax_Syntax.pos
                                                           = uu___7;
                                                         FStarC_Syntax_Syntax.hash_code
                                                           = uu___8;_},
                                                       uu___9)::[] ->
                                                        ((w
                                                            FStarC_Syntax_Util.t_true),
                                                          false)
                                                    | ({
                                                         FStarC_Syntax_Syntax.n
                                                           =
                                                           FStarC_Syntax_Syntax.Tm_constant
                                                           (FStarC_Const.Const_bool
                                                           false);
                                                         FStarC_Syntax_Syntax.pos
                                                           = uu___7;
                                                         FStarC_Syntax_Syntax.hash_code
                                                           = uu___8;_},
                                                       uu___9)::[] ->
                                                        ((w
                                                            FStarC_Syntax_Util.t_false),
                                                          false)
                                                    | uu___7 -> (tm1, false))
                                                 else
                                                   if
                                                     FStarC_Syntax_Syntax.fv_eq_lid
                                                       fv
                                                       FStarC_Parser_Const.haseq_lid
                                                   then
                                                     (let t_has_eq_for_sure t
                                                        =
                                                        let haseq_lids =
                                                          [FStarC_Parser_Const.int_lid;
                                                          FStarC_Parser_Const.bool_lid;
                                                          FStarC_Parser_Const.unit_lid;
                                                          FStarC_Parser_Const.string_lid] in
                                                        let uu___7 =
                                                          let uu___8 =
                                                            FStarC_Syntax_Subst.compress
                                                              t in
                                                          uu___8.FStarC_Syntax_Syntax.n in
                                                        match uu___7 with
                                                        | FStarC_Syntax_Syntax.Tm_fvar
                                                            fv1 when
                                                            FStarC_List.existsb
                                                              (fun l ->
                                                                 FStarC_Syntax_Syntax.fv_eq_lid
                                                                   fv1 l)
                                                              haseq_lids
                                                            -> true
                                                        | uu___8 -> false in
                                                      if
                                                        (FStarC_List.length
                                                           args)
                                                          = Prims.int_one
                                                      then
                                                        let t =
                                                          FStar_Pervasives_Native.fst
                                                            (FStarC_List.hd
                                                               args) in
                                                        let uu___7 =
                                                          t_has_eq_for_sure t in
                                                        (if uu___7
                                                         then
                                                           ((w
                                                               FStarC_Syntax_Util.t_true),
                                                             false)
                                                         else
                                                           (let uu___8 =
                                                              let uu___9 =
                                                                FStarC_Syntax_Subst.compress
                                                                  t in
                                                              uu___9.FStarC_Syntax_Syntax.n in
                                                            match uu___8 with
                                                            | FStarC_Syntax_Syntax.Tm_refine
                                                                uu___9 ->
                                                                let t1 =
                                                                  FStarC_Syntax_Util.unrefine
                                                                    t in
                                                                let uu___10 =
                                                                  t_has_eq_for_sure
                                                                    t1 in
                                                                if uu___10
                                                                then
                                                                  ((w
                                                                    FStarC_Syntax_Util.t_true),
                                                                    false)
                                                                else
                                                                  (let haseq_tm
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    tm1 in
                                                                    uu___12.FStarC_Syntax_Syntax.n in
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_app
                                                                    {
                                                                    FStarC_Syntax_Syntax.hd
                                                                    = hd1;
                                                                    FStarC_Syntax_Syntax.arg
                                                                    = uu___12;_}
                                                                    -> hd1
                                                                    | 
                                                                    uu___12
                                                                    ->
                                                                    FStarC_Effect.failwith
                                                                    "Impossible! We have already checked that this is a Tm_app" in
                                                                   let uu___11
                                                                    =
                                                                    FStarC_Syntax_Util.mk_app
                                                                    haseq_tm
                                                                    [
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    t1] in
                                                                   (uu___11,
                                                                    false))
                                                            | uu___9 ->
                                                                (tm1, false)))
                                                      else (tm1, false))
                                                   else
                                                     (let uu___7 =
                                                        reduce_equality
                                                          (norm_cb cfg) cfg
                                                          env1 in
                                                      uu___7 tm1)
                             | uu___7 -> (tm1, false)))
                   | FStarC_Syntax_Syntax.Tm_refine
                       { FStarC_Syntax_Syntax.b2 = bv;
                         FStarC_Syntax_Syntax.phi = t;_}
                       ->
                       let uu___4 = simp_t t in
                       (match uu___4 with
                        | FStar_Pervasives_Native.Some true ->
                            ((bv.FStarC_Syntax_Syntax.sort), false)
                        | FStar_Pervasives_Native.Some false -> (tm1, false)
                        | FStar_Pervasives_Native.None -> (tm1, false))
                   | FStarC_Syntax_Syntax.Tm_match uu___4 ->
                       let uu___5 = is_const_match tm1 in
                       (match uu___5 with
                        | FStar_Pervasives_Native.Some true ->
                            ((w FStarC_Syntax_Util.t_true), false)
                        | FStar_Pervasives_Native.Some false ->
                            ((w FStarC_Syntax_Util.t_false), false)
                        | FStar_Pervasives_Native.None -> (tm1, false))
                   | uu___4 -> (tm1, false))))
and rebuild (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env) (stack1 : stack)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  FStarC_TypeChecker_Cfg.log cfg
    (fun uu___1 ->
       (let uu___3 =
          FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t in
        let uu___4 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
        let uu___5 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_nat
            (FStarC_List.length env1) in
        let uu___6 =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_list showable_stack_elt)
            (FStar_Pervasives_Native.fst (firstn (Prims.of_int 4) stack1)) in
        FStarC_Format.print4
          ">>> %s\nRebuild %s with %s env elements and top of the stack %s\n"
          uu___3 uu___4 uu___5 uu___6);
       (let uu___3 = FStarC_Effect.op_Bang dbg_NormRebuild in
        if uu___3
        then
          let uu___4 = FStarC_Syntax_Util.unbound_variables t in
          match uu___4 with
          | [] -> ()
          | bvs ->
              ((let uu___6 =
                  FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                    t in
                let uu___7 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
                let uu___8 =
                  FStarC_Class_Show.show
                    (FStarC_Class_Show.show_list
                       FStarC_Syntax_Print.showable_bv) bvs in
                FStarC_Format.print3 "!!! Rebuild (%s) %s, free vars=%s\n"
                  uu___6 uu___7 uu___8);
               FStarC_Effect.failwith "DIE!")
        else ()));
  (let f_opt = is_fext_on_domain t in
   if
     (match f_opt with
      | FStar_Pervasives_Native.Some v -> true
      | uu___1 -> false) &&
       (match stack1 with | (Arg uu___1)::uu___2 -> true | uu___1 -> false)
   then let uu___1 = FStarC_Option.must f_opt in norm cfg env1 stack1 uu___1
   else
     (let uu___1 = maybe_simplify cfg env1 stack1 t in
      match uu___1 with
      | (t1, renorm) ->
          if renorm
          then norm cfg env1 stack1 t1
          else
            (let uu___2 = FStarC_Syntax_Util.hua t1 in
             match uu___2 with
             | FStar_Pervasives_Native.None -> do_rebuild cfg env1 stack1 t1
             | FStar_Pervasives_Native.Some hua ->
                 let uu___3 = hua in
                 (match uu___3 with
                  | (h, uu___4, args) ->
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = FStarC_Syntax_Syntax.fv_to_tm h in
                          disc_proj_head cfg uu___7 in
                        match uu___6 with
                        | FStar_Pervasives_Native.Some
                            (d, is_disc, n_indexed, idx) when
                            (FStarC_List.length args) > n_indexed ->
                            let uu___7 =
                              reduce_disc_proj cfg d is_disc idx
                                (FStar_Pervasives_Native.fst
                                   (FStarC_List.nth args n_indexed)) in
                            (match uu___7 with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some field ->
                                 let uu___8 =
                                   FStarC_Util.first_N
                                     (n_indexed + Prims.int_one) args in
                                 (match uu___8 with
                                  | (uu___9, rest) ->
                                      FStar_Pervasives_Native.Some
                                        (field, rest)))
                        | uu___7 -> FStar_Pervasives_Native.None in
                      (match uu___5 with
                       | FStar_Pervasives_Native.Some (field, rest) ->
                           (FStarC_TypeChecker_Cfg.log cfg
                              (fun uu___7 ->
                                 let uu___8 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_term t1 in
                                 let uu___9 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_term field in
                                 FStarC_Format.print2
                                   "Reduced projector/discriminator %s to %s\n"
                                   uu___8 uu___9);
                            (let stack_has_arg =
                               match stack1 with
                               | (Arg uu___7)::uu___8 -> true
                               | uu___7 -> false in
                             if
                               (match rest with
                                | [] -> true
                                | uu___7 -> false) &&
                                 (Prims.not stack_has_arg)
                             then do_rebuild cfg env1 stack1 field
                             else
                               (let uu___7 =
                                  FStarC_Syntax_Util.mk_app field rest in
                                norm cfg env1 stack1 uu___7)))
                       | FStar_Pervasives_Native.None ->
                           let uu___6 = check_strict cfg hua in
                           (match uu___6 with
                            | FStar_Pervasives_Native.Some force ->
                                let uu___7 = hua in
                                (match uu___7 with
                                 | (h1, u, a) ->
                                     (FStarC_TypeChecker_Cfg.log cfg
                                        (fun uu___9 ->
                                           let uu___10 =
                                             FStarC_Class_Show.show
                                               FStarC_Syntax_Print.showable_term
                                               t1 in
                                           FStarC_Format.print1
                                             "Strict application detected, trying to unfold the head: %s\n"
                                             uu___10);
                                      (let fv =
                                         FStarC_Syntax_Syntax.lid_of_fv h1 in
                                       let qninfo =
                                         FStarC_TypeChecker_Env.lookup_qname
                                           cfg.FStarC_TypeChecker_Cfg.tcenv
                                           fv in
                                       let defn =
                                         FStarC_TypeChecker_Env.lookup_definition_qninfo
                                           cfg.FStarC_TypeChecker_Cfg.delta_level
                                           h1.FStarC_Syntax_Syntax.fv_name
                                           qninfo in
                                       if
                                         match defn with
                                         | FStar_Pervasives_Native.None ->
                                             true
                                         | uu___9 -> false
                                       then do_rebuild cfg env1 stack1 t1
                                       else
                                         (let cfg_zeta =
                                            {
                                              FStarC_TypeChecker_Cfg.steps =
                                                (let uu___9 =
                                                   cfg.FStarC_TypeChecker_Cfg.steps in
                                                 {
                                                   FStarC_TypeChecker_Cfg.beta
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.beta);
                                                   FStarC_TypeChecker_Cfg.iota
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.iota);
                                                   FStarC_TypeChecker_Cfg.zeta
                                                     = true;
                                                   FStarC_TypeChecker_Cfg.zeta_full
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.zeta_full);
                                                   FStarC_TypeChecker_Cfg.weak
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.weak);
                                                   FStarC_TypeChecker_Cfg.hnf
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.hnf);
                                                   FStarC_TypeChecker_Cfg.primops
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.primops);
                                                   FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                                   FStarC_TypeChecker_Cfg.unfold_until
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.unfold_until);
                                                   FStarC_TypeChecker_Cfg.unfold_only
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.unfold_only);
                                                   FStarC_TypeChecker_Cfg.unfold_once
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.unfold_once);
                                                   FStarC_TypeChecker_Cfg.unfold_fully
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.unfold_fully);
                                                   FStarC_TypeChecker_Cfg.unfold_attr
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.unfold_attr);
                                                   FStarC_TypeChecker_Cfg.unfold_qual
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.unfold_qual);
                                                   FStarC_TypeChecker_Cfg.unfold_namespace
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.unfold_namespace);
                                                   FStarC_TypeChecker_Cfg.dont_unfold_attr
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                                                   FStarC_TypeChecker_Cfg.pure_subterms_within_computations
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                                                   FStarC_TypeChecker_Cfg.simplify
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.simplify);
                                                   FStarC_TypeChecker_Cfg.erase_universes
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.erase_universes);
                                                   FStarC_TypeChecker_Cfg.allow_unbound_universes
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                                                   FStarC_TypeChecker_Cfg.reify_
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.reify_);
                                                   FStarC_TypeChecker_Cfg.compress_uvars
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.compress_uvars);
                                                   FStarC_TypeChecker_Cfg.no_full_norm
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.no_full_norm);
                                                   FStarC_TypeChecker_Cfg.check_no_uvars
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.check_no_uvars);
                                                   FStarC_TypeChecker_Cfg.unmeta
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.unmeta);
                                                   FStarC_TypeChecker_Cfg.unascribe
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.unascribe);
                                                   FStarC_TypeChecker_Cfg.in_full_norm_request
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.in_full_norm_request);
                                                   FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                                   FStarC_TypeChecker_Cfg.nbe_step
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.nbe_step);
                                                   FStarC_TypeChecker_Cfg.for_extraction
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.for_extraction);
                                                   FStarC_TypeChecker_Cfg.unrefine
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.unrefine);
                                                   FStarC_TypeChecker_Cfg.default_univs_to_zero
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                                                   FStarC_TypeChecker_Cfg.tactics
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.tactics);
                                                   FStarC_TypeChecker_Cfg.reduce_projections
                                                     =
                                                     (uu___9.FStarC_TypeChecker_Cfg.reduce_projections)
                                                 });
                                              FStarC_TypeChecker_Cfg.tcenv =
                                                (cfg.FStarC_TypeChecker_Cfg.tcenv);
                                              FStarC_TypeChecker_Cfg.debug =
                                                (cfg.FStarC_TypeChecker_Cfg.debug);
                                              FStarC_TypeChecker_Cfg.delta_level
                                                =
                                                (cfg.FStarC_TypeChecker_Cfg.delta_level);
                                              FStarC_TypeChecker_Cfg.primitive_steps
                                                =
                                                (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
                                              FStarC_TypeChecker_Cfg.strong =
                                                (cfg.FStarC_TypeChecker_Cfg.strong);
                                              FStarC_TypeChecker_Cfg.memoize_lazy
                                                =
                                                (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
                                              FStarC_TypeChecker_Cfg.normalize_pure_lets
                                                =
                                                (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
                                              FStarC_TypeChecker_Cfg.reifying
                                                =
                                                (cfg.FStarC_TypeChecker_Cfg.reifying);
                                              FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg
                                                =
                                                (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                                            } in
                                          let uu___9 =
                                            if force
                                            then true
                                            else
                                              (let uu___10 =
                                                 FStarC_TypeChecker_Normalize_Unfolding.should_unfold
                                                   true cfg_zeta
                                                   (fun uu___11 -> false) h1
                                                   qninfo in
                                               match uu___10 with
                                               | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_yes
                                                   -> true
                                               | uu___11 -> false) in
                                          if uu___9
                                          then
                                            let stack2 =
                                              FStarC_List.fold_right
                                                (fun arg acc ->
                                                   let memo =
                                                     fresh_cfg_memo () in
                                                   let uu___10 =
                                                     let uu___11 =
                                                       let uu___12 =
                                                         FStarC_Class_HasRange.pos
                                                           (FStarC_Syntax_Syntax.has_range_syntax
                                                              ())
                                                           (FStar_Pervasives_Native.fst
                                                              arg) in
                                                       ((Clos
                                                           (env1,
                                                             (FStar_Pervasives_Native.fst
                                                                arg), memo,
                                                             false)),
                                                         (FStar_Pervasives_Native.snd
                                                            arg), uu___12) in
                                                     Arg uu___11 in
                                                   uu___10 :: acc) a stack1 in
                                            let stack3 =
                                              if
                                                match u with
                                                | hd::tl -> true
                                                | uu___10 -> false
                                              then
                                                (UnivArgs
                                                   (u,
                                                     (t1.FStarC_Syntax_Syntax.pos)))
                                                :: stack2
                                              else stack2 in
                                            let t0 =
                                              FStarC_Syntax_Syntax.fv_to_tm
                                                h1 in
                                            (FStarC_TypeChecker_Cfg.log cfg
                                               (fun uu___11 ->
                                                  let uu___12 =
                                                    FStarC_Class_Show.show
                                                      FStarC_Syntax_Print.showable_term
                                                      t0 in
                                                  let uu___13 =
                                                    FStarC_Class_Show.show
                                                      (FStarC_Class_Show.show_list
                                                         showable_stack_elt)
                                                      stack3 in
                                                  FStarC_Format.print2
                                                    "Continuing with t=%s, stack=%s\n"
                                                    uu___12 uu___13);
                                             do_unfold_fv cfg stack3 t0
                                               qninfo h1)
                                          else do_rebuild cfg env1 stack1 t1))))
                            | FStar_Pervasives_Native.None ->
                                do_rebuild cfg env1 stack1 t1))))))
and do_rebuild (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (stack1 : stack) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  match stack1 with
  | [] -> t
  | (Meta (uu___, m, r))::stack2 ->
      let t1 =
        match m with
        | FStarC_Syntax_Syntax.Meta_monadic uu___1 ->
            let uu___2 =
              let uu___3 = FStarC_Syntax_Subst.compress t in
              uu___3.FStarC_Syntax_Syntax.n in
            (match uu___2 with
             | FStarC_Syntax_Syntax.Tm_meta
                 { FStarC_Syntax_Syntax.tm2 = t';
                   FStarC_Syntax_Syntax.meta =
                     FStarC_Syntax_Syntax.Meta_monadic uu___3;_}
                 ->
                 FStarC_Syntax_Syntax.mk
                   (FStarC_Syntax_Syntax.Tm_meta
                      {
                        FStarC_Syntax_Syntax.tm2 = t';
                        FStarC_Syntax_Syntax.meta = m
                      }) r
             | uu___3 ->
                 FStarC_Syntax_Syntax.mk
                   (FStarC_Syntax_Syntax.Tm_meta
                      {
                        FStarC_Syntax_Syntax.tm2 = t;
                        FStarC_Syntax_Syntax.meta = m
                      }) r)
        | uu___1 ->
            FStarC_Syntax_Syntax.mk
              (FStarC_Syntax_Syntax.Tm_meta
                 {
                   FStarC_Syntax_Syntax.tm2 = t;
                   FStarC_Syntax_Syntax.meta = m
                 }) r in
      rebuild cfg env1 stack2 t1
  | (MemoLazy r)::stack2 ->
      (set_memo cfg r (env1, t);
       FStarC_TypeChecker_Cfg.log cfg
         (fun uu___2 ->
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
            FStarC_Format.print1 "\tSet memo %s\n" uu___3);
       rebuild cfg env1 stack2 t)
  | (Let (env', bs, lb, r))::stack2 ->
      let body = FStarC_Syntax_Subst.close bs t in
      let t1 =
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_let
             {
               FStarC_Syntax_Syntax.lbs = (false, [lb]);
               FStarC_Syntax_Syntax.body1 = body
             }) r in
      rebuild cfg env' stack2 t1
  | (Abs (env', bs, env'', lopt, r))::stack2 ->
      let bs1 = norm_binders cfg env' bs in
      let lopt1 = FStarC_Option.map (norm_residual_comp cfg env'') lopt in
      let uu___ =
        let uu___1 = FStarC_Syntax_Util.abs bs1 t lopt1 in
        {
          FStarC_Syntax_Syntax.n = (uu___1.FStarC_Syntax_Syntax.n);
          FStarC_Syntax_Syntax.pos = r;
          FStarC_Syntax_Syntax.hash_code =
            (uu___1.FStarC_Syntax_Syntax.hash_code)
        } in
      rebuild cfg env1 stack2 uu___
  | (Arg (Univ uu___, uu___1, uu___2))::uu___3 ->
      FStarC_Effect.failwith "Impossible"
  | (Arg (Dummy, uu___, uu___1))::uu___2 ->
      FStarC_Effect.failwith "Impossible"
  | (UnivArgs (us, r))::stack2 ->
      let t1 = FStarC_Syntax_Syntax.mk_Tm_uinst t us in
      rebuild cfg env1 stack2 t1
  | (Arg (Clos (env_arg, tm, uu___, uu___1), aq, r))::stack2 when
      let uu___2 = head_of t in
      FStarC_Syntax_Util.is_fstar_tactics_by_tactic uu___2 ->
      let t1 =
        let uu___2 =
          let uu___3 = closure_as_term cfg env_arg tm in (uu___3, aq) in
        FStarC_Syntax_Syntax.extend_app t uu___2 r in
      rebuild cfg env1 stack2 t1
  | (Arg (Clos (env_arg, tm, m, uu___), aq, r))::stack2 ->
      (FStarC_TypeChecker_Cfg.log cfg
         (fun uu___2 ->
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tm in
            FStarC_Format.print1 "Rebuilding with arg %s\n" uu___3);
       (let uu___2 =
          if (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.hnf
          then let uu___3 = is_partial_primop_app cfg t in Prims.not uu___3
          else false in
        if uu___2
        then
          let arg = closure_as_term cfg env_arg tm in
          let t1 = FStarC_Syntax_Syntax.extend_app t (arg, aq) r in
          rebuild cfg env_arg stack2 t1
        else
          (let uu___3 = read_memo cfg m in
           match uu___3 with
           | FStar_Pervasives_Native.Some (uu___4, a) ->
               let t1 = FStarC_Syntax_Syntax.extend_app t (a, aq) r in
               rebuild cfg env_arg stack2 t1
           | FStar_Pervasives_Native.None when
               Prims.not
                 (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.iota
               ->
               let stack3 = (App (env1, t, aq, r)) :: stack2 in
               norm cfg env_arg stack3 tm
           | FStar_Pervasives_Native.None ->
               let stack3 = (MemoLazy m) :: (App (env1, t, aq, r)) :: stack2 in
               norm cfg env_arg stack3 tm)))
  | (App (env2, head, aq, r))::stack' when should_reify cfg stack1 ->
      let t0 = t in
      let fallback msg uu___ =
        FStarC_TypeChecker_Cfg.log cfg
          (fun uu___2 ->
             let uu___3 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
             FStarC_Format.print2 "Not reifying%s: %s\n" msg uu___3);
        (let t1 = FStarC_Syntax_Syntax.extend_app head (t, aq) r in
         rebuild cfg env2 stack' t1) in
      let is_non_tac_layered_effect m = false in
      let uu___ =
        let uu___1 = FStarC_Syntax_Subst.compress t in
        uu___1.FStarC_Syntax_Syntax.n in
      (match uu___ with
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = uu___1;
             FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic
               (m, uu___2);_}
           when
           (is_non_tac_layered_effect m) &&
             (Prims.not
                (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction)
           ->
           fallback
             (FStarC_Format.fmt1
                "Meta_monadic for a non-TAC layered effect %s in non-extraction mode"
                (FStarC_Ident.string_of_lid m)) ()
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = uu___1;
             FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic
               (m, uu___2);_}
           when
           if
             (is_non_tac_layered_effect m) &&
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
           then
             let uu___3 =
               get_extraction_mode cfg.FStarC_TypeChecker_Cfg.tcenv m in
             match uu___3 with
             | FStarC_Syntax_Syntax.Extract_none _0 -> true
             | uu___4 -> false
           else false ->
           let uu___3 =
             get_extraction_mode cfg.FStarC_TypeChecker_Cfg.tcenv m in
           (match uu___3 with
            | FStarC_Syntax_Syntax.Extract_none msg ->
                FStarC_Errors.raise_error
                  (FStarC_Syntax_Syntax.has_range_syntax ()) t
                  FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                  (Obj.magic
                     (FStarC_Format.fmt2
                        "Normalizer cannot reify effect %s for extraction since %s"
                        (FStarC_Ident.string_of_lid m) msg)))
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = uu___1;
             FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic
               (m, uu___2);_}
           when
           if
             (is_non_tac_layered_effect m) &&
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
           then
             let uu___3 =
               get_extraction_mode cfg.FStarC_TypeChecker_Cfg.tcenv m in
             uu___3 = FStarC_Syntax_Syntax.Extract_primitive
           else false ->
           fallback
             (FStarC_Format.fmt1
                "Meta_monadic for a non-TAC layered effect %s which is Extract_primtiive"
                (FStarC_Ident.string_of_lid m)) ()
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = uu___1;
             FStarC_Syntax_Syntax.meta =
               FStarC_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, uu___2);_}
           when
           ((is_non_tac_layered_effect msrc) ||
              (is_non_tac_layered_effect mtgt))
             &&
             (Prims.not
                (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction)
           ->
           fallback
             (FStarC_Format.fmt2
                "Meta_monadic_lift for a non-TAC layered effect %s ~> %s in non extraction mode"
                (FStarC_Ident.string_of_lid msrc)
                (FStarC_Ident.string_of_lid mtgt)) ()
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = uu___1;
             FStarC_Syntax_Syntax.meta =
               FStarC_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, uu___2);_}
           when
           if
             (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
           then
             let uu___3 =
               if is_non_tac_layered_effect msrc
               then
                 let uu___4 =
                   get_extraction_mode cfg.FStarC_TypeChecker_Cfg.tcenv msrc in
                 match uu___4 with
                 | FStarC_Syntax_Syntax.Extract_none _0 -> true
                 | uu___5 -> false
               else false in
             (if uu___3
              then true
              else
                if is_non_tac_layered_effect mtgt
                then
                  (let uu___4 =
                     get_extraction_mode cfg.FStarC_TypeChecker_Cfg.tcenv
                       mtgt in
                   match uu___4 with
                   | FStarC_Syntax_Syntax.Extract_none _0 -> true
                   | uu___5 -> false)
                else false)
           else false ->
           FStarC_Errors.raise_error
             (FStarC_Syntax_Syntax.has_range_syntax ()) t
             FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_string)
             (Obj.magic
                (FStarC_Format.fmt2
                   "Normalizer cannot reify %s ~> %s for extraction"
                   (FStarC_Ident.string_of_lid msrc)
                   (FStarC_Ident.string_of_lid mtgt)))
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = t1;
             FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic
               (m, ty);_}
           -> do_reify_monadic (fallback " (1)") cfg env2 stack1 t1 m ty
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = t1;
             FStarC_Syntax_Syntax.meta =
               FStarC_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, ty);_}
           ->
           let lifted =
             let uu___1 = closure_as_term cfg env2 ty in
             reify_lift cfg t1 msrc mtgt uu___1 in
           (FStarC_TypeChecker_Cfg.log cfg
              (fun uu___2 ->
                 let uu___3 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     lifted in
                 FStarC_Format.print1 "Reified lift to (1): %s\n" uu___3);
            norm cfg env2 (FStarC_List.tl stack1) lifted)
       | FStarC_Syntax_Syntax.Tm_app
           {
             FStarC_Syntax_Syntax.hd =
               {
                 FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                   (FStarC_Const.Const_reflect uu___1);
                 FStarC_Syntax_Syntax.pos = uu___2;
                 FStarC_Syntax_Syntax.hash_code = uu___3;_};
             FStarC_Syntax_Syntax.arg = (e, uu___4);_}
           -> norm cfg env2 stack' e
       | FStarC_Syntax_Syntax.Tm_app uu___1 when
           (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.primops
           ->
           let uu___2 = FStarC_Syntax_Util.head_and_args_full_unmeta t in
           (match uu___2 with
            | (hd, args) ->
                let uu___3 =
                  let uu___4 = FStarC_Syntax_Util.un_uinst hd in
                  uu___4.FStarC_Syntax_Syntax.n in
                (match uu___3 with
                 | FStarC_Syntax_Syntax.Tm_fvar fv ->
                     let uu___4 =
                       FStarC_TypeChecker_Cfg.find_prim_step cfg fv in
                     (match uu___4 with
                      | FStar_Pervasives_Native.Some
                          { FStarC_TypeChecker_Primops_Base.name = uu___5;
                            FStarC_TypeChecker_Primops_Base.arity = uu___6;
                            FStarC_TypeChecker_Primops_Base.univ_arity =
                              uu___7;
                            FStarC_TypeChecker_Primops_Base.auto_reflect =
                              FStar_Pervasives_Native.Some n;
                            FStarC_TypeChecker_Primops_Base.strong_reduction_ok
                              = uu___8;
                            FStarC_TypeChecker_Primops_Base.requires_binder_substitution
                              = uu___9;
                            FStarC_TypeChecker_Primops_Base.renorm_after =
                              uu___10;
                            FStarC_TypeChecker_Primops_Base.interpretation =
                              uu___11;
                            FStarC_TypeChecker_Primops_Base.interpretation_nbe
                              = uu___12;_}
                          when (FStarC_List.length args) = n ->
                          norm cfg env2 stack' t
                      | uu___5 -> fallback " (3)" ())
                 | uu___4 -> fallback " (4)" ()))
       | uu___1 -> fallback " (2)" ())
  | (App (env2, head, aq, r))::stack2 ->
      let t1 = FStarC_Syntax_Syntax.extend_app head (t, aq) r in
      rebuild cfg env2 stack2 t1
  | (CBVApp (env', head, aq, r))::stack2 ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = fresh_cfg_memo () in (env1, t, uu___5, false) in
              Clos uu___4 in
            (uu___3, aq, (t.FStarC_Syntax_Syntax.pos)) in
          Arg uu___2 in
        uu___1 :: stack2 in
      norm cfg env' uu___ head
  | (Match (env', asc_opt, branches1, lopt, cfg1, r))::stack2 ->
      let lopt1 = FStarC_Option.map (norm_residual_comp cfg1 env') lopt in
      (FStarC_TypeChecker_Cfg.log cfg1
         (fun uu___1 ->
            let uu___2 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
            FStarC_Format.print1
              "Rebuilding with match, scrutinee is %s ...\n" uu___2);
       (let scrutinee_env = env1 in
        let env2 = env' in
        let scrutinee = t in
        let norm_and_rebuild_match uu___1 =
          FStarC_TypeChecker_Cfg.log cfg1
            (fun uu___3 ->
               let uu___4 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                   scrutinee in
               let uu___5 =
                 let uu___6 =
                   FStarC_List.map
                     (fun uu___7 ->
                        match uu___7 with
                        | (p, uu___8, uu___9) ->
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_pat p) branches1 in
                 FStarC_String.concat "\n\t" uu___6 in
               FStarC_Format.print2
                 "match is irreducible: scrutinee=%s\nbranches=%s\n" uu___4
                 uu___5);
          (let whnf =
             (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
               ||
               (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.hnf in
           let cfg_exclude_zeta =
             if
               (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta_full
             then cfg1
             else
               (let new_delta =
                  FStarC_List.filter
                    (fun uu___3 ->
                       match uu___3 with
                       | FStarC_TypeChecker_Env.InliningDelta -> true
                       | FStarC_TypeChecker_Env.Eager_unfolding_only -> true
                       | uu___4 -> false)
                    cfg1.FStarC_TypeChecker_Cfg.delta_level in
                let steps =
                  let uu___3 = cfg1.FStarC_TypeChecker_Cfg.steps in
                  {
                    FStarC_TypeChecker_Cfg.beta =
                      (uu___3.FStarC_TypeChecker_Cfg.beta);
                    FStarC_TypeChecker_Cfg.iota =
                      (uu___3.FStarC_TypeChecker_Cfg.iota);
                    FStarC_TypeChecker_Cfg.zeta = false;
                    FStarC_TypeChecker_Cfg.zeta_full =
                      (uu___3.FStarC_TypeChecker_Cfg.zeta_full);
                    FStarC_TypeChecker_Cfg.weak =
                      (uu___3.FStarC_TypeChecker_Cfg.weak);
                    FStarC_TypeChecker_Cfg.hnf =
                      (uu___3.FStarC_TypeChecker_Cfg.hnf);
                    FStarC_TypeChecker_Cfg.primops =
                      (uu___3.FStarC_TypeChecker_Cfg.primops);
                    FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                      (uu___3.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                    FStarC_TypeChecker_Cfg.unfold_until =
                      FStar_Pervasives_Native.None;
                    FStarC_TypeChecker_Cfg.unfold_only =
                      FStar_Pervasives_Native.None;
                    FStarC_TypeChecker_Cfg.unfold_once =
                      (uu___3.FStarC_TypeChecker_Cfg.unfold_once);
                    FStarC_TypeChecker_Cfg.unfold_fully =
                      (uu___3.FStarC_TypeChecker_Cfg.unfold_fully);
                    FStarC_TypeChecker_Cfg.unfold_attr =
                      FStar_Pervasives_Native.None;
                    FStarC_TypeChecker_Cfg.unfold_qual =
                      FStar_Pervasives_Native.None;
                    FStarC_TypeChecker_Cfg.unfold_namespace =
                      FStar_Pervasives_Native.None;
                    FStarC_TypeChecker_Cfg.dont_unfold_attr =
                      FStar_Pervasives_Native.None;
                    FStarC_TypeChecker_Cfg.pure_subterms_within_computations
                      =
                      (uu___3.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                    FStarC_TypeChecker_Cfg.simplify =
                      (uu___3.FStarC_TypeChecker_Cfg.simplify);
                    FStarC_TypeChecker_Cfg.erase_universes =
                      (uu___3.FStarC_TypeChecker_Cfg.erase_universes);
                    FStarC_TypeChecker_Cfg.allow_unbound_universes =
                      (uu___3.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                    FStarC_TypeChecker_Cfg.reify_ =
                      (uu___3.FStarC_TypeChecker_Cfg.reify_);
                    FStarC_TypeChecker_Cfg.compress_uvars =
                      (uu___3.FStarC_TypeChecker_Cfg.compress_uvars);
                    FStarC_TypeChecker_Cfg.no_full_norm =
                      (uu___3.FStarC_TypeChecker_Cfg.no_full_norm);
                    FStarC_TypeChecker_Cfg.check_no_uvars =
                      (uu___3.FStarC_TypeChecker_Cfg.check_no_uvars);
                    FStarC_TypeChecker_Cfg.unmeta =
                      (uu___3.FStarC_TypeChecker_Cfg.unmeta);
                    FStarC_TypeChecker_Cfg.unascribe =
                      (uu___3.FStarC_TypeChecker_Cfg.unascribe);
                    FStarC_TypeChecker_Cfg.in_full_norm_request =
                      (uu___3.FStarC_TypeChecker_Cfg.in_full_norm_request);
                    FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                      (uu___3.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                    FStarC_TypeChecker_Cfg.nbe_step =
                      (uu___3.FStarC_TypeChecker_Cfg.nbe_step);
                    FStarC_TypeChecker_Cfg.for_extraction =
                      (uu___3.FStarC_TypeChecker_Cfg.for_extraction);
                    FStarC_TypeChecker_Cfg.unrefine =
                      (uu___3.FStarC_TypeChecker_Cfg.unrefine);
                    FStarC_TypeChecker_Cfg.default_univs_to_zero =
                      (uu___3.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                    FStarC_TypeChecker_Cfg.tactics =
                      (uu___3.FStarC_TypeChecker_Cfg.tactics);
                    FStarC_TypeChecker_Cfg.reduce_projections =
                      (uu___3.FStarC_TypeChecker_Cfg.reduce_projections)
                  } in
                {
                  FStarC_TypeChecker_Cfg.steps = steps;
                  FStarC_TypeChecker_Cfg.tcenv =
                    (cfg1.FStarC_TypeChecker_Cfg.tcenv);
                  FStarC_TypeChecker_Cfg.debug =
                    (cfg1.FStarC_TypeChecker_Cfg.debug);
                  FStarC_TypeChecker_Cfg.delta_level = new_delta;
                  FStarC_TypeChecker_Cfg.primitive_steps =
                    (cfg1.FStarC_TypeChecker_Cfg.primitive_steps);
                  FStarC_TypeChecker_Cfg.strong = true;
                  FStarC_TypeChecker_Cfg.memoize_lazy =
                    (cfg1.FStarC_TypeChecker_Cfg.memoize_lazy);
                  FStarC_TypeChecker_Cfg.normalize_pure_lets =
                    (cfg1.FStarC_TypeChecker_Cfg.normalize_pure_lets);
                  FStarC_TypeChecker_Cfg.reifying =
                    (cfg1.FStarC_TypeChecker_Cfg.reifying);
                  FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                    (cfg1.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                }) in
           let norm_or_whnf env3 t1 =
             if whnf
             then closure_as_term cfg_exclude_zeta env3 t1
             else norm cfg_exclude_zeta env3 [] t1 in
           let rec norm_pat env3 p =
             match p.FStarC_Syntax_Syntax.v with
             | FStarC_Syntax_Syntax.Pat_constant uu___3 -> (p, env3)
             | FStarC_Syntax_Syntax.Pat_cons (fv, us_opt, pats) ->
                 let us_opt1 =
                   if
                     (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.erase_universes
                   then FStar_Pervasives_Native.None
                   else
                     (match us_opt with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some us ->
                          let uu___3 =
                            FStarC_List.map (norm_universe cfg1 env3) us in
                          FStar_Pervasives_Native.Some uu___3) in
                 let uu___3 =
                   FStarC_List.fold_left
                     (fun uu___4 uu___5 ->
                        match (uu___4, uu___5) with
                        | ((pats1, env4), (p1, b)) ->
                            let uu___6 = norm_pat env4 p1 in
                            (match uu___6 with
                             | (p2, env5) -> (((p2, b) :: pats1), env5)))
                     ([], env3) pats in
                 (match uu___3 with
                  | (pats1, env4) ->
                      ({
                         FStarC_Syntax_Syntax.v =
                           (FStarC_Syntax_Syntax.Pat_cons
                              (fv, us_opt1, (FStarC_List.rev pats1)));
                         FStarC_Syntax_Syntax.p = (p.FStarC_Syntax_Syntax.p)
                       }, env4))
             | FStarC_Syntax_Syntax.Pat_var x ->
                 let x1 =
                   let uu___3 = norm_or_whnf env3 x.FStarC_Syntax_Syntax.sort in
                   {
                     FStarC_Syntax_Syntax.ppname =
                       (x.FStarC_Syntax_Syntax.ppname);
                     FStarC_Syntax_Syntax.index =
                       (x.FStarC_Syntax_Syntax.index);
                     FStarC_Syntax_Syntax.sort = uu___3
                   } in
                 let uu___3 = let uu___4 = dummy () in uu___4 :: env3 in
                 ({
                    FStarC_Syntax_Syntax.v =
                      (FStarC_Syntax_Syntax.Pat_var x1);
                    FStarC_Syntax_Syntax.p = (p.FStarC_Syntax_Syntax.p)
                  }, uu___3)
             | FStarC_Syntax_Syntax.Pat_dot_term eopt ->
                 let eopt1 = FStarC_Option.map (norm_or_whnf env3) eopt in
                 ({
                    FStarC_Syntax_Syntax.v =
                      (FStarC_Syntax_Syntax.Pat_dot_term eopt1);
                    FStarC_Syntax_Syntax.p = (p.FStarC_Syntax_Syntax.p)
                  }, env3) in
           let norm_branches uu___3 =
             match env2 with
             | [] when whnf -> branches1
             | uu___4 ->
                 FStarC_List.map
                   (fun branch ->
                      let uu___5 = FStarC_Syntax_Subst.open_branch branch in
                      match uu___5 with
                      | (p, wopt, e) ->
                          let uu___6 = norm_pat env2 p in
                          (match uu___6 with
                           | (p1, env3) ->
                               let wopt1 =
                                 match wopt with
                                 | FStar_Pervasives_Native.None ->
                                     FStar_Pervasives_Native.None
                                 | FStar_Pervasives_Native.Some w ->
                                     let uu___7 = norm_or_whnf env3 w in
                                     FStar_Pervasives_Native.Some uu___7 in
                               let e1 = norm_or_whnf env3 e in
                               FStarC_Syntax_Util.branch (p1, wopt1, e1)))
                   branches1 in
           let maybe_commute_matches uu___3 =
             let can_commute =
               match branches1 with
               | ({
                    FStarC_Syntax_Syntax.v = FStarC_Syntax_Syntax.Pat_cons
                      (fv, uu___4, uu___5);
                    FStarC_Syntax_Syntax.p = uu___6;_},
                  uu___7, uu___8)::uu___9 ->
                   FStarC_TypeChecker_Env.fv_has_attr
                     cfg1.FStarC_TypeChecker_Cfg.tcenv fv
                     FStarC_Parser_Const.commute_nested_matches_lid
               | uu___4 -> false in
             let uu___4 =
               let uu___5 = FStarC_Syntax_Util.unascribe scrutinee in
               uu___5.FStarC_Syntax_Syntax.n in
             match uu___4 with
             | FStarC_Syntax_Syntax.Tm_match
                 { FStarC_Syntax_Syntax.scrutinee = sc0;
                   FStarC_Syntax_Syntax.ret_opt = asc_opt0;
                   FStarC_Syntax_Syntax.brs = branches0;
                   FStarC_Syntax_Syntax.rc_opt1 = lopt0;_}
                 when can_commute ->
                 let reduce_branch b =
                   let stack3 =
                     [Match (env', asc_opt, branches1, lopt1, cfg1, r)] in
                   let uu___5 = FStarC_Syntax_Subst.open_branch b in
                   match uu___5 with
                   | (p, wopt, e) ->
                       let uu___6 = norm_pat scrutinee_env p in
                       (match uu___6 with
                        | (p1, branch_env) ->
                            let wopt1 =
                              match wopt with
                              | FStar_Pervasives_Native.None ->
                                  FStar_Pervasives_Native.None
                              | FStar_Pervasives_Native.Some w ->
                                  let uu___7 = norm_or_whnf branch_env w in
                                  FStar_Pervasives_Native.Some uu___7 in
                            let e1 = norm cfg1 branch_env stack3 e in
                            FStarC_Syntax_Util.branch (p1, wopt1, e1)) in
                 let branches01 = FStarC_List.map reduce_branch branches0 in
                 let uu___5 =
                   FStarC_Syntax_Syntax.mk
                     (FStarC_Syntax_Syntax.Tm_match
                        {
                          FStarC_Syntax_Syntax.scrutinee = sc0;
                          FStarC_Syntax_Syntax.ret_opt = asc_opt0;
                          FStarC_Syntax_Syntax.brs = branches01;
                          FStarC_Syntax_Syntax.rc_opt1 = lopt0
                        }) r in
                 rebuild cfg1 env2 stack2 uu___5
             | uu___5 ->
                 let scrutinee1 =
                   let uu___6 =
                     if
                       (((cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.iota
                           &&
                           (Prims.not
                              (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak))
                          &&
                          (Prims.not
                             (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.compress_uvars))
                         &&
                         (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee
                     then maybe_weakly_reduced scrutinee
                     else false in
                   if uu___6
                   then
                     norm
                       {
                         FStarC_TypeChecker_Cfg.steps =
                           (let uu___7 = cfg1.FStarC_TypeChecker_Cfg.steps in
                            {
                              FStarC_TypeChecker_Cfg.beta =
                                (uu___7.FStarC_TypeChecker_Cfg.beta);
                              FStarC_TypeChecker_Cfg.iota =
                                (uu___7.FStarC_TypeChecker_Cfg.iota);
                              FStarC_TypeChecker_Cfg.zeta =
                                (uu___7.FStarC_TypeChecker_Cfg.zeta);
                              FStarC_TypeChecker_Cfg.zeta_full =
                                (uu___7.FStarC_TypeChecker_Cfg.zeta_full);
                              FStarC_TypeChecker_Cfg.weak =
                                (uu___7.FStarC_TypeChecker_Cfg.weak);
                              FStarC_TypeChecker_Cfg.hnf =
                                (uu___7.FStarC_TypeChecker_Cfg.hnf);
                              FStarC_TypeChecker_Cfg.primops =
                                (uu___7.FStarC_TypeChecker_Cfg.primops);
                              FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets
                                =
                                (uu___7.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                              FStarC_TypeChecker_Cfg.unfold_until =
                                (uu___7.FStarC_TypeChecker_Cfg.unfold_until);
                              FStarC_TypeChecker_Cfg.unfold_only =
                                (uu___7.FStarC_TypeChecker_Cfg.unfold_only);
                              FStarC_TypeChecker_Cfg.unfold_once =
                                (uu___7.FStarC_TypeChecker_Cfg.unfold_once);
                              FStarC_TypeChecker_Cfg.unfold_fully =
                                (uu___7.FStarC_TypeChecker_Cfg.unfold_fully);
                              FStarC_TypeChecker_Cfg.unfold_attr =
                                (uu___7.FStarC_TypeChecker_Cfg.unfold_attr);
                              FStarC_TypeChecker_Cfg.unfold_qual =
                                (uu___7.FStarC_TypeChecker_Cfg.unfold_qual);
                              FStarC_TypeChecker_Cfg.unfold_namespace =
                                (uu___7.FStarC_TypeChecker_Cfg.unfold_namespace);
                              FStarC_TypeChecker_Cfg.dont_unfold_attr =
                                (uu___7.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                              FStarC_TypeChecker_Cfg.pure_subterms_within_computations
                                =
                                (uu___7.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                              FStarC_TypeChecker_Cfg.simplify =
                                (uu___7.FStarC_TypeChecker_Cfg.simplify);
                              FStarC_TypeChecker_Cfg.erase_universes =
                                (uu___7.FStarC_TypeChecker_Cfg.erase_universes);
                              FStarC_TypeChecker_Cfg.allow_unbound_universes
                                =
                                (uu___7.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                              FStarC_TypeChecker_Cfg.reify_ =
                                (uu___7.FStarC_TypeChecker_Cfg.reify_);
                              FStarC_TypeChecker_Cfg.compress_uvars =
                                (uu___7.FStarC_TypeChecker_Cfg.compress_uvars);
                              FStarC_TypeChecker_Cfg.no_full_norm =
                                (uu___7.FStarC_TypeChecker_Cfg.no_full_norm);
                              FStarC_TypeChecker_Cfg.check_no_uvars =
                                (uu___7.FStarC_TypeChecker_Cfg.check_no_uvars);
                              FStarC_TypeChecker_Cfg.unmeta =
                                (uu___7.FStarC_TypeChecker_Cfg.unmeta);
                              FStarC_TypeChecker_Cfg.unascribe =
                                (uu___7.FStarC_TypeChecker_Cfg.unascribe);
                              FStarC_TypeChecker_Cfg.in_full_norm_request =
                                (uu___7.FStarC_TypeChecker_Cfg.in_full_norm_request);
                              FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee
                                = false;
                              FStarC_TypeChecker_Cfg.nbe_step =
                                (uu___7.FStarC_TypeChecker_Cfg.nbe_step);
                              FStarC_TypeChecker_Cfg.for_extraction =
                                (uu___7.FStarC_TypeChecker_Cfg.for_extraction);
                              FStarC_TypeChecker_Cfg.unrefine =
                                (uu___7.FStarC_TypeChecker_Cfg.unrefine);
                              FStarC_TypeChecker_Cfg.default_univs_to_zero =
                                (uu___7.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                              FStarC_TypeChecker_Cfg.tactics =
                                (uu___7.FStarC_TypeChecker_Cfg.tactics);
                              FStarC_TypeChecker_Cfg.reduce_projections =
                                (uu___7.FStarC_TypeChecker_Cfg.reduce_projections)
                            });
                         FStarC_TypeChecker_Cfg.tcenv =
                           (cfg1.FStarC_TypeChecker_Cfg.tcenv);
                         FStarC_TypeChecker_Cfg.debug =
                           (cfg1.FStarC_TypeChecker_Cfg.debug);
                         FStarC_TypeChecker_Cfg.delta_level =
                           (cfg1.FStarC_TypeChecker_Cfg.delta_level);
                         FStarC_TypeChecker_Cfg.primitive_steps =
                           (cfg1.FStarC_TypeChecker_Cfg.primitive_steps);
                         FStarC_TypeChecker_Cfg.strong =
                           (cfg1.FStarC_TypeChecker_Cfg.strong);
                         FStarC_TypeChecker_Cfg.memoize_lazy =
                           (cfg1.FStarC_TypeChecker_Cfg.memoize_lazy);
                         FStarC_TypeChecker_Cfg.normalize_pure_lets =
                           (cfg1.FStarC_TypeChecker_Cfg.normalize_pure_lets);
                         FStarC_TypeChecker_Cfg.reifying =
                           (cfg1.FStarC_TypeChecker_Cfg.reifying);
                         FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                           (cfg1.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                       } scrutinee_env [] scrutinee
                   else scrutinee in
                 let asc_opt1 = norm_match_returns cfg1 env2 asc_opt in
                 let branches2 = norm_branches () in
                 let uu___6 =
                   FStarC_Syntax_Syntax.mk
                     (FStarC_Syntax_Syntax.Tm_match
                        {
                          FStarC_Syntax_Syntax.scrutinee = scrutinee1;
                          FStarC_Syntax_Syntax.ret_opt = asc_opt1;
                          FStarC_Syntax_Syntax.brs = branches2;
                          FStarC_Syntax_Syntax.rc_opt1 = lopt1
                        }) r in
                 rebuild cfg1 env2 stack2 uu___6 in
           maybe_commute_matches ()) in
        let rec is_cons head =
          let uu___1 =
            let uu___2 = FStarC_Syntax_Subst.compress head in
            uu___2.FStarC_Syntax_Syntax.n in
          match uu___1 with
          | FStarC_Syntax_Syntax.Tm_uinst (h, uu___2) -> is_cons h
          | FStarC_Syntax_Syntax.Tm_constant uu___2 -> true
          | FStarC_Syntax_Syntax.Tm_fvar
              { FStarC_Syntax_Syntax.fv_name = uu___2;
                FStarC_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                  (FStarC_Syntax_Syntax.Data_ctor);_}
              -> true
          | FStarC_Syntax_Syntax.Tm_fvar
              { FStarC_Syntax_Syntax.fv_name = uu___2;
                FStarC_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                  (FStarC_Syntax_Syntax.Record_ctor uu___3);_}
              -> true
          | uu___2 -> false in
        let guard_when_clause wopt b rest =
          match wopt with
          | FStar_Pervasives_Native.None -> b
          | FStar_Pervasives_Native.Some w ->
              let then_branch = b in
              let else_branch =
                FStarC_Syntax_Syntax.mk
                  (FStarC_Syntax_Syntax.Tm_match
                     {
                       FStarC_Syntax_Syntax.scrutinee = scrutinee;
                       FStarC_Syntax_Syntax.ret_opt = asc_opt;
                       FStarC_Syntax_Syntax.brs = rest;
                       FStarC_Syntax_Syntax.rc_opt1 = lopt1
                     }) r in
              FStarC_Syntax_Util.if_then_else w then_branch else_branch in
        let rec matches_pat scrutinee_orig p =
          let scrutinee1 = FStarC_Syntax_Util.unmeta scrutinee_orig in
          let scrutinee2 = FStarC_Syntax_Util.unlazy scrutinee1 in
          let uu___1 = FStarC_Syntax_Util.head_and_args_full scrutinee2 in
          match uu___1 with
          | (head, args) ->
              (match p.FStarC_Syntax_Syntax.v with
               | FStarC_Syntax_Syntax.Pat_var bv ->
                   FStar_Pervasives.Inl [(bv, scrutinee_orig)]
               | FStarC_Syntax_Syntax.Pat_dot_term uu___2 ->
                   FStar_Pervasives.Inl []
               | FStarC_Syntax_Syntax.Pat_constant s ->
                   (match scrutinee2.FStarC_Syntax_Syntax.n with
                    | FStarC_Syntax_Syntax.Tm_constant s' when
                        FStarC_Const.eq_const s s' -> FStar_Pervasives.Inl []
                    | uu___2 ->
                        let uu___3 =
                          let uu___4 = is_cons head in Prims.not uu___4 in
                        FStar_Pervasives.Inr uu___3)
               | FStarC_Syntax_Syntax.Pat_cons (fv, uu___2, arg_pats) ->
                   let uu___3 =
                     let uu___4 = FStarC_Syntax_Util.un_uinst head in
                     uu___4.FStarC_Syntax_Syntax.n in
                   (match uu___3 with
                    | FStarC_Syntax_Syntax.Tm_fvar fv' when
                        FStarC_Syntax_Syntax.fv_eq fv fv' ->
                        matches_args [] args arg_pats
                    | uu___4 ->
                        let uu___5 =
                          let uu___6 = is_cons head in Prims.not uu___6 in
                        FStar_Pervasives.Inr uu___5))
        and matches_args out a p =
          match (a, p) with
          | ([], []) -> FStar_Pervasives.Inl out
          | ((t1, uu___1)::rest_a, (p1, uu___2)::rest_p) ->
              let uu___3 = matches_pat t1 p1 in
              (match uu___3 with
               | FStar_Pervasives.Inl s ->
                   matches_args (FStarC_List.op_At out s) rest_a rest_p
               | m -> m)
          | uu___1 -> FStar_Pervasives.Inr false in
        let rec matches scrutinee1 p =
          match p with
          | [] -> norm_and_rebuild_match ()
          | (p1, wopt, b)::rest ->
              let uu___1 = matches_pat scrutinee1 p1 in
              (match uu___1 with
               | FStar_Pervasives.Inr false -> matches scrutinee1 rest
               | FStar_Pervasives.Inr true -> norm_and_rebuild_match ()
               | FStar_Pervasives.Inl s ->
                   (FStarC_TypeChecker_Cfg.log cfg1
                      (fun uu___3 ->
                         let uu___4 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_pat p1 in
                         let uu___5 =
                           let uu___6 =
                             FStarC_List.map
                               (fun uu___7 ->
                                  match uu___7 with
                                  | (uu___8, t1) ->
                                      FStarC_Class_Show.show
                                        FStarC_Syntax_Print.showable_term t1)
                               s in
                           FStarC_String.concat "; " uu___6 in
                         FStarC_Format.print2
                           "Matches pattern %s with subst = %s\n" uu___4
                           uu___5);
                    (let env0 = env2 in
                     let env3 =
                       FStarC_List.fold_left
                         (fun env4 uu___3 ->
                            match uu___3 with
                            | (bv, t1) ->
                                let m = fresh_cfg_memo () in
                                (if
                                   Prims.not
                                     (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.hnf
                                 then
                                   ((let uu___6 =
                                       let uu___7 =
                                         let uu___8 = weak_cfg cfg1 in
                                         (uu___8, ([], t1)) in
                                       FStar_Pervasives_Native.Some uu___7 in
                                     FStarC_Effect.op_Colon_Equals
                                       m.weak_memo uu___6);
                                    if
                                      Prims.not
                                        (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
                                    then
                                      FStarC_Effect.op_Colon_Equals
                                        m.strong_memo
                                        (FStar_Pervasives_Native.Some
                                           (cfg1, ([], t1)))
                                    else ())
                                 else ();
                                 (let uu___5 =
                                    let uu___6 = fresh_memo () in
                                    ((FStar_Pervasives_Native.Some
                                        (FStarC_Syntax_Syntax.mk_binder bv)),
                                      (Clos ([], t1, m, false)), uu___6) in
                                  uu___5 :: env4))) env2 s in
                     let uu___3 = guard_when_clause wopt b rest in
                     norm cfg1 env3 stack2 uu___3))) in
        if (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.iota
        then matches scrutinee branches1
        else norm_and_rebuild_match ()))
and norm_match_returns (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (ret_opt :
    FStarC_Syntax_Syntax.match_returns_ascription
      FStar_Pervasives_Native.option)
  :
  (FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.ascription)
    FStar_Pervasives_Native.option=
  match ret_opt with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (b, asc) ->
      let b1 = norm_binder cfg env1 b in
      let uu___ = FStarC_Syntax_Subst.open_ascription [b1] asc in
      (match uu___ with
       | (subst, asc1) ->
           let asc2 =
             let uu___1 = let uu___2 = dummy () in uu___2 :: env1 in
             norm_ascription cfg uu___1 asc1 in
           let uu___1 =
             let uu___2 = FStarC_Syntax_Subst.close_ascription subst asc2 in
             (b1, uu___2) in
           FStar_Pervasives_Native.Some uu___1)
and norm_ascription (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (asc :
    ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
      FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
      FStar_Pervasives.either * FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax FStar_Pervasives_Native.option *
      Prims.bool))
  : FStarC_Syntax_Syntax.ascription=
  let uu___ = asc in
  match uu___ with
  | (tc, tacopt, use_eq) ->
      let uu___1 =
        match tc with
        | FStar_Pervasives.Inl t ->
            let uu___2 = norm cfg env1 [] t in FStar_Pervasives.Inl uu___2
        | FStar_Pervasives.Inr c ->
            let uu___2 = norm_comp cfg env1 c in FStar_Pervasives.Inr uu___2 in
      let uu___2 = FStarC_Option.map (norm cfg env1 []) tacopt in
      (uu___1, uu___2, use_eq)
and norm_residual_comp (cfg : FStarC_TypeChecker_Cfg.cfg) (env1 : env)
  (rc : FStarC_Syntax_Syntax.residual_comp) :
  FStarC_Syntax_Syntax.residual_comp=
  let uu___ =
    FStarC_Option.map (closure_as_term cfg env1)
      rc.FStarC_Syntax_Syntax.residual_typ in
  {
    FStarC_Syntax_Syntax.residual_effect =
      (rc.FStarC_Syntax_Syntax.residual_effect);
    FStarC_Syntax_Syntax.residual_typ = uu___;
    FStarC_Syntax_Syntax.residual_flags =
      (rc.FStarC_Syntax_Syntax.residual_flags)
  }
let reflection_env_hook :
  FStarC_TypeChecker_Env.env FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let normalize_with_primitive_steps
  (ps : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list)
  (s : FStarC_TypeChecker_Env.steps) (e : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  FStarC_Stats.record "norm_term"
    (fun uu___ ->
       let is_nbe = is_nbe_request s in
       let maybe_nbe = if is_nbe then " (NBE)" else "" in
       FStarC_Errors.with_ctx
         (Prims.strcat "While normalizing a term" maybe_nbe)
         (fun uu___1 ->
            FStarC_Profiling.profile
              (fun uu___2 ->
                 let c = FStarC_TypeChecker_Cfg.config' ps s e in
                 FStarC_Effect.op_Colon_Equals reflection_env_hook
                   (FStar_Pervasives_Native.Some e);
                 FStarC_Effect.op_Colon_Equals plugin_unfold_warn_ctr
                   Prims.int_one;
                 FStarC_TypeChecker_Cfg.log_top c
                   (fun uu___6 ->
                      let uu___7 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term t in
                      FStarC_Format.print2
                        "\nStarting normalizer%s for (%s) {\n" maybe_nbe
                        uu___7);
                 FStarC_TypeChecker_Cfg.log_top c
                   (fun uu___7 ->
                      let uu___8 =
                        FStarC_Class_Show.show
                          FStarC_TypeChecker_Cfg.showable_cfg c in
                      FStarC_Format.print1 ">>> cfg = %s\n" uu___8);
                 FStarC_Defensive.def_check_scoped
                   FStarC_TypeChecker_Env.hasBinders_env
                   FStarC_Class_Binders.hasNames_term
                   FStarC_Syntax_Print.pretty_term t.FStarC_Syntax_Syntax.pos
                   "normalize_with_primitive_steps call" e t;
                 (let uu___8 =
                    FStarC_Timing.record_ms
                      (fun uu___9 ->
                         if is_nbe then nbe_eval c s t else norm c [] [] t) in
                  match uu___8 with
                  | (r, ms) ->
                      (FStarC_TypeChecker_Cfg.log_top c
                         (fun uu___10 ->
                            let uu___11 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_term r in
                            let uu___12 =
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_int ms in
                            FStarC_Format.print3
                              "}\nNormalization%s result = (%s) in %s ms\n"
                              maybe_nbe uu___11 uu___12);
                       r)))
              (FStar_Pervasives_Native.Some
                 (FStarC_Ident.string_of_lid
                    (FStarC_TypeChecker_Env.current_module e)))
              "FStarC.TypeChecker.Normalize.normalize_with_primitive_steps"))
let normalize (s : FStarC_TypeChecker_Env.steps)
  (e : FStarC_TypeChecker_Env.env) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  FStarC_Profiling.profile
    (fun uu___ -> normalize_with_primitive_steps [] s e t)
    (FStar_Pervasives_Native.Some
       (FStarC_Ident.string_of_lid (FStarC_TypeChecker_Env.current_module e)))
    "FStarC.TypeChecker.Normalize.normalize"
let normalize_comp (s : FStarC_TypeChecker_Env.steps)
  (e : FStarC_TypeChecker_Env.env) (c : FStarC_Syntax_Syntax.comp) :
  FStarC_Syntax_Syntax.comp=
  FStarC_Stats.record "norm_comp"
    (fun uu___ ->
       FStarC_Profiling.profile
         (fun uu___1 ->
            let cfg = FStarC_TypeChecker_Cfg.config s e in
            FStarC_Effect.op_Colon_Equals reflection_env_hook
              (FStar_Pervasives_Native.Some e);
            FStarC_Effect.op_Colon_Equals plugin_unfold_warn_ctr
              Prims.int_one;
            FStarC_TypeChecker_Cfg.log_top cfg
              (fun uu___5 ->
                 let uu___6 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp c in
                 FStarC_Format.print1
                   "Starting normalizer for computation (%s) {\n" uu___6);
            FStarC_TypeChecker_Cfg.log_top cfg
              (fun uu___6 ->
                 let uu___7 =
                   FStarC_Class_Show.show FStarC_TypeChecker_Cfg.showable_cfg
                     cfg in
                 FStarC_Format.print1 ">>> cfg = %s\n" uu___7);
            FStarC_Defensive.def_check_scoped
              FStarC_TypeChecker_Env.hasBinders_env
              FStarC_Class_Binders.hasNames_comp
              FStarC_Syntax_Print.pretty_comp c.FStarC_Syntax_Syntax.pos
              "normalize_comp call" e c;
            (let uu___7 =
               FStarC_Errors.with_ctx "While normalizing a computation type"
                 (fun uu___8 ->
                    FStarC_Timing.record_ms
                      (fun uu___9 -> norm_comp cfg [] c)) in
             match uu___7 with
             | (c1, ms) ->
                 (FStarC_TypeChecker_Cfg.log_top cfg
                    (fun uu___9 ->
                       let uu___10 =
                         FStarC_Class_Show.show
                           FStarC_Syntax_Print.showable_comp c1 in
                       let uu___11 =
                         FStarC_Class_Show.show
                           FStarC_Class_Show.showable_int ms in
                       FStarC_Format.print2
                         "}\nNormalization result = (%s) in %s ms\n" uu___10
                         uu___11);
                  c1)))
         (FStar_Pervasives_Native.Some
            (FStarC_Ident.string_of_lid
               (FStarC_TypeChecker_Env.current_module e)))
         "FStarC.TypeChecker.Normalize.normalize_comp")
let normalize_universe (env1 : FStarC_TypeChecker_Env.env)
  (u : FStarC_Syntax_Syntax.universe) : FStarC_Syntax_Syntax.universe=
  FStarC_Errors.with_ctx "While normalizing a universe level"
    (fun uu___ ->
       let uu___1 = FStarC_TypeChecker_Cfg.config [] env1 in
       norm_universe uu___1 [] u)
let non_info_norm (env1 : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : Prims.bool=
  let steps =
    [FStarC_TypeChecker_Env.UnfoldUntil FStarC_Syntax_Syntax.delta_constant;
    FStarC_TypeChecker_Env.AllowUnboundUniverses;
    FStarC_TypeChecker_Env.EraseUniverses;
    FStarC_TypeChecker_Env.Primops;
    FStarC_TypeChecker_Env.Beta;
    FStarC_TypeChecker_Env.Iota;
    FStarC_TypeChecker_Env.HNF;
    FStarC_TypeChecker_Env.Unascribe;
    FStarC_TypeChecker_Env.ForExtraction] in
  let uu___ = normalize steps env1 t in
  FStarC_TypeChecker_Env.non_informative env1 uu___
let maybe_promote_t (env1 : FStarC_TypeChecker_Env.env)
  (non_informative_only : Prims.bool) (t : FStarC_Syntax_Syntax.term) :
  Prims.bool=
  if Prims.not non_informative_only then true else non_info_norm env1 t
let ghost_to_pure_aux (env1 : FStarC_TypeChecker_Env.env)
  (non_informative_only : Prims.bool)
  (c : FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax) :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax=
  match c.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Total uu___ -> c
  | FStarC_Syntax_Syntax.GTotal t ->
      let uu___ = maybe_promote_t env1 non_informative_only t in
      if uu___
      then
        {
          FStarC_Syntax_Syntax.n = (FStarC_Syntax_Syntax.Total t);
          FStarC_Syntax_Syntax.pos = (c.FStarC_Syntax_Syntax.pos);
          FStarC_Syntax_Syntax.hash_code = (c.FStarC_Syntax_Syntax.hash_code)
        }
      else c
  | FStarC_Syntax_Syntax.Comp ct ->
      let l =
        FStarC_TypeChecker_Env.norm_eff_name env1
          ct.FStarC_Syntax_Syntax.effect_name in
      let uu___ =
        if FStarC_Syntax_Util.is_ghost_effect l
        then
          maybe_promote_t env1 non_informative_only
            ct.FStarC_Syntax_Syntax.result_typ
        else false in
      if uu___
      then
        let ct1 =
          match downgrade_ghost_effect_name
                  ct.FStarC_Syntax_Syntax.effect_name
          with
          | FStar_Pervasives_Native.Some pure_eff ->
              let flags =
                if
                  FStarC_Ident.lid_equals pure_eff
                    FStarC_Parser_Const.effect_Tot_lid
                then FStarC_Syntax_Syntax.TOTAL ::
                  (ct.FStarC_Syntax_Syntax.flags)
                else ct.FStarC_Syntax_Syntax.flags in
              {
                FStarC_Syntax_Syntax.comp_univs =
                  (ct.FStarC_Syntax_Syntax.comp_univs);
                FStarC_Syntax_Syntax.effect_name = pure_eff;
                FStarC_Syntax_Syntax.result_typ =
                  (ct.FStarC_Syntax_Syntax.result_typ);
                FStarC_Syntax_Syntax.comp_pre =
                  (ct.FStarC_Syntax_Syntax.comp_pre);
                FStarC_Syntax_Syntax.comp_post =
                  (ct.FStarC_Syntax_Syntax.comp_post);
                FStarC_Syntax_Syntax.flags = flags
              }
          | FStar_Pervasives_Native.None ->
              let ct2 = FStarC_TypeChecker_Env.unfold_effect_abbrev env1 c in
              {
                FStarC_Syntax_Syntax.comp_univs =
                  (ct2.FStarC_Syntax_Syntax.comp_univs);
                FStarC_Syntax_Syntax.effect_name =
                  FStarC_Parser_Const.effect_PURE_lid;
                FStarC_Syntax_Syntax.result_typ =
                  (ct2.FStarC_Syntax_Syntax.result_typ);
                FStarC_Syntax_Syntax.comp_pre =
                  (ct2.FStarC_Syntax_Syntax.comp_pre);
                FStarC_Syntax_Syntax.comp_post =
                  (ct2.FStarC_Syntax_Syntax.comp_post);
                FStarC_Syntax_Syntax.flags = (ct2.FStarC_Syntax_Syntax.flags)
              } in
        {
          FStarC_Syntax_Syntax.n = (FStarC_Syntax_Syntax.Comp ct1);
          FStarC_Syntax_Syntax.pos = (c.FStarC_Syntax_Syntax.pos);
          FStarC_Syntax_Syntax.hash_code = (c.FStarC_Syntax_Syntax.hash_code)
        }
      else c
  | uu___ -> c
let ghost_to_pure_lcomp_aux (env1 : FStarC_TypeChecker_Env.env)
  (non_informative_only : Prims.bool) (lc : FStarC_TypeChecker_Common.lcomp)
  : FStarC_TypeChecker_Common.lcomp=
  let uu___ =
    if
      FStarC_Syntax_Util.is_ghost_effect
        lc.FStarC_TypeChecker_Common.eff_name
    then
      maybe_promote_t env1 non_informative_only
        lc.FStarC_TypeChecker_Common.res_typ
    else false in
  if uu___
  then
    match downgrade_ghost_effect_name lc.FStarC_TypeChecker_Common.eff_name
    with
    | FStar_Pervasives_Native.Some pure_eff ->
        let uu___1 =
          FStarC_TypeChecker_Common.apply_lcomp
            (ghost_to_pure_aux env1 non_informative_only) (fun g -> g) lc in
        {
          FStarC_TypeChecker_Common.eff_name = pure_eff;
          FStarC_TypeChecker_Common.res_typ =
            (uu___1.FStarC_TypeChecker_Common.res_typ);
          FStarC_TypeChecker_Common.cflags =
            (uu___1.FStarC_TypeChecker_Common.cflags);
          FStarC_TypeChecker_Common.comp_thunk =
            (uu___1.FStarC_TypeChecker_Common.comp_thunk)
        }
    | FStar_Pervasives_Native.None -> lc
  else lc
let maybe_ghost_to_pure (env1 : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp) : FStarC_Syntax_Syntax.comp=
  ghost_to_pure_aux env1 true c
let maybe_ghost_to_pure_lcomp (env1 : FStarC_TypeChecker_Env.env)
  (lc : FStarC_TypeChecker_Common.lcomp) : FStarC_TypeChecker_Common.lcomp=
  ghost_to_pure_lcomp_aux env1 true lc
let ghost_to_pure (env1 : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax) :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax=
  ghost_to_pure_aux env1 false c
let ghost_to_pure_lcomp (env1 : FStarC_TypeChecker_Env.env)
  (lc : FStarC_TypeChecker_Common.lcomp) : FStarC_TypeChecker_Common.lcomp=
  ghost_to_pure_lcomp_aux env1 false lc
let ghost_to_pure2 (env1 : FStarC_TypeChecker_Env.env)
  (uu___ : (FStarC_Syntax_Syntax.comp * FStarC_Syntax_Syntax.comp)) :
  (FStarC_Syntax_Syntax.comp * FStarC_Syntax_Syntax.comp)=
  match uu___ with
  | (c1, c2) ->
      let uu___1 =
        let uu___2 = maybe_ghost_to_pure env1 c1 in
        let uu___3 = maybe_ghost_to_pure env1 c2 in (uu___2, uu___3) in
      (match uu___1 with
       | (c11, c21) ->
           let c1_eff =
             FStarC_TypeChecker_Env.norm_eff_name env1
               (FStarC_Syntax_Util.comp_effect_name c11) in
           let c2_eff =
             FStarC_TypeChecker_Env.norm_eff_name env1
               (FStarC_Syntax_Util.comp_effect_name c21) in
           if FStarC_Ident.lid_equals c1_eff c2_eff
           then (c11, c21)
           else
             (let c1_erasable =
                FStarC_TypeChecker_Env.is_erasable_effect env1 c1_eff in
              let c2_erasable =
                FStarC_TypeChecker_Env.is_erasable_effect env1 c2_eff in
              if
                c1_erasable &&
                  (FStarC_Ident.lid_equals c2_eff
                     FStarC_Parser_Const.effect_GHOST_lid)
              then let uu___2 = ghost_to_pure env1 c21 in (c11, uu___2)
              else
                if
                  c2_erasable &&
                    (FStarC_Ident.lid_equals c1_eff
                       FStarC_Parser_Const.effect_GHOST_lid)
                then (let uu___2 = ghost_to_pure env1 c11 in (uu___2, c21))
                else (c11, c21)))
let ghost_to_pure_lcomp2 (env1 : FStarC_TypeChecker_Env.env)
  (uu___ :
    (FStarC_TypeChecker_Common.lcomp * FStarC_TypeChecker_Common.lcomp))
  : (FStarC_TypeChecker_Common.lcomp * FStarC_TypeChecker_Common.lcomp)=
  match uu___ with
  | (lc1, lc2) ->
      let uu___1 =
        let uu___2 = maybe_ghost_to_pure_lcomp env1 lc1 in
        let uu___3 = maybe_ghost_to_pure_lcomp env1 lc2 in (uu___2, uu___3) in
      (match uu___1 with
       | (lc11, lc21) ->
           let lc1_eff =
             FStarC_TypeChecker_Env.norm_eff_name env1
               lc11.FStarC_TypeChecker_Common.eff_name in
           let lc2_eff =
             FStarC_TypeChecker_Env.norm_eff_name env1
               lc21.FStarC_TypeChecker_Common.eff_name in
           if FStarC_Ident.lid_equals lc1_eff lc2_eff
           then (lc11, lc21)
           else
             (let lc1_erasable =
                FStarC_TypeChecker_Env.is_erasable_effect env1 lc1_eff in
              let lc2_erasable =
                FStarC_TypeChecker_Env.is_erasable_effect env1 lc2_eff in
              if
                lc1_erasable &&
                  (FStarC_Ident.lid_equals lc2_eff
                     FStarC_Parser_Const.effect_GHOST_lid)
              then
                let uu___2 = ghost_to_pure_lcomp env1 lc21 in (lc11, uu___2)
              else
                if
                  lc2_erasable &&
                    (FStarC_Ident.lid_equals lc1_eff
                       FStarC_Parser_Const.effect_GHOST_lid)
                then
                  (let uu___2 = ghost_to_pure_lcomp env1 lc11 in
                   (uu___2, lc21))
                else (lc11, lc21)))
let warn_norm_failure (r : FStarC_Range_Type.t) (e : Prims.exn) : unit=
  let uu___ =
    let uu___1 = FStarC_Util.message_of_exn e in
    FStarC_Format.fmt1 "Normalization failed with error %s\n" uu___1 in
  FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range r
    FStarC_Errors_Codes.Warning_NormalizationFailure ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_string) (Obj.magic uu___)
let term_to_doc (env1 : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : FStar_Pprint.document=
  let t1 =
    try
      (fun uu___ ->
         match () with
         | () ->
             normalize [FStarC_TypeChecker_Env.AllowUnboundUniverses] env1 t)
        ()
    with | uu___ -> (warn_norm_failure t.FStarC_Syntax_Syntax.pos uu___; t) in
  let env' =
    FStarC_Syntax_DsEnv.set_current_module env1.FStarC_TypeChecker_Env.dsenv
      env1.FStarC_TypeChecker_Env.curmodule in
  let env'1 =
    let uu___ = FStarC_Options.interactive () in
    if uu___ then env' else FStarC_Syntax_DsEnv.clear_scope_mods env' in
  FStarC_Syntax_Print.term_to_doc' env'1 t1
let term_to_string (env1 : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : Prims.string=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let t1 =
         try
           (fun uu___1 ->
              match () with
              | () ->
                  normalize [FStarC_TypeChecker_Env.AllowUnboundUniverses]
                    env1 t) ()
         with
         | uu___1 -> (warn_norm_failure t.FStarC_Syntax_Syntax.pos uu___1; t) in
       FStarC_Syntax_Print.term_to_string'
         (FStarC_Syntax_DsEnv.set_current_module
            env1.FStarC_TypeChecker_Env.dsenv
            env1.FStarC_TypeChecker_Env.curmodule) t1)
let comp_to_string (env1 : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp) : Prims.string=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let c1 =
         try
           (fun uu___1 ->
              match () with
              | () ->
                  let uu___2 =
                    FStarC_TypeChecker_Cfg.config
                      [FStarC_TypeChecker_Env.AllowUnboundUniverses] env1 in
                  norm_comp uu___2 [] c) ()
         with
         | uu___1 -> (warn_norm_failure c.FStarC_Syntax_Syntax.pos uu___1; c) in
       FStarC_Syntax_Print.comp_to_string'
         (FStarC_Syntax_DsEnv.set_current_module
            env1.FStarC_TypeChecker_Env.dsenv
            env1.FStarC_TypeChecker_Env.curmodule) c1)
let comp_to_doc (env1 : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp) : FStar_Pprint.document=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let c1 =
         try
           (fun uu___1 ->
              match () with
              | () ->
                  let uu___2 =
                    FStarC_TypeChecker_Cfg.config
                      [FStarC_TypeChecker_Env.AllowUnboundUniverses] env1 in
                  norm_comp uu___2 [] c) ()
         with
         | uu___1 -> (warn_norm_failure c.FStarC_Syntax_Syntax.pos uu___1; c) in
       FStarC_Syntax_Print.comp_to_doc'
         (FStarC_Syntax_DsEnv.set_current_module
            env1.FStarC_TypeChecker_Env.dsenv
            env1.FStarC_TypeChecker_Env.curmodule) c1)
let normalize_refinement (steps : FStarC_TypeChecker_Env.steps)
  (env1 : FStarC_TypeChecker_Env.env) (t0 : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.typ=
  let t =
    normalize (FStarC_List.op_At steps [FStarC_TypeChecker_Env.Beta]) env1 t0 in
  FStarC_Syntax_Util.flatten_refinement t
let whnf_steps : FStarC_TypeChecker_Env.step Prims.list=
  [FStarC_TypeChecker_Env.Primops;
  FStarC_TypeChecker_Env.Weak;
  FStarC_TypeChecker_Env.HNF;
  FStarC_TypeChecker_Env.UnfoldUntil FStarC_Syntax_Syntax.delta_constant;
  FStarC_TypeChecker_Env.Beta]
let unfold_whnf' (steps : FStarC_TypeChecker_Env.steps)
  (env1 : FStarC_TypeChecker_Env.env) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  normalize (FStarC_List.op_At steps whnf_steps) env1 t
let unfold_whnf (env1 : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  unfold_whnf' [] env1 t
let reduce_or_remove_uvar_solutions (remove : Prims.bool)
  (env1 : FStarC_TypeChecker_Env.env) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  normalize
    (FStarC_List.op_At
       (if remove
        then
          [FStarC_TypeChecker_Env.DefaultUnivsToZero;
          FStarC_TypeChecker_Env.CheckNoUvars]
        else [])
       [FStarC_TypeChecker_Env.Beta;
       FStarC_TypeChecker_Env.DoNotUnfoldPureLets;
       FStarC_TypeChecker_Env.CompressUvars;
       FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta;
       FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Iota;
       FStarC_TypeChecker_Env.NoFullNorm]) env1 t
let reduce_uvar_solutions (env1 : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  reduce_or_remove_uvar_solutions false env1 t
let remove_uvar_solutions (env1 : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  reduce_or_remove_uvar_solutions true env1 t
let eta_expand_with_type (env1 : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term) (t_e : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.term=
  let uu___ = FStarC_Syntax_Util.arrow_formals_comp t_e in
  match uu___ with
  | (formals, c) ->
      (match formals with
       | [] -> e
       | uu___1 ->
           let uu___2 = FStarC_Syntax_Util.abs_formals e in
           (match uu___2 with
            | (actuals, uu___3, uu___4) ->
                if
                  (FStarC_List.length actuals) = (FStarC_List.length formals)
                then e
                else
                  (let uu___5 = FStarC_Syntax_Util.args_of_binders formals in
                   match uu___5 with
                   | (binders, args) ->
                       let uu___6 =
                         FStarC_Syntax_Syntax.mk_Tm_app e args
                           e.FStarC_Syntax_Syntax.pos in
                       let uu___7 =
                         let uu___8 =
                           FStarC_Syntax_Util.residual_comp_of_comp c in
                         FStar_Pervasives_Native.Some uu___8 in
                       FStarC_Syntax_Util.abs binders uu___6 uu___7)))
let eta_expand (env1 : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  match t.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_name x ->
      eta_expand_with_type env1 t x.FStarC_Syntax_Syntax.sort
  | uu___ ->
      let uu___1 = FStarC_Syntax_Util.head_and_args_full t in
      (match uu___1 with
       | (head, args) ->
           let uu___2 =
             let uu___3 = FStarC_Syntax_Subst.compress head in
             uu___3.FStarC_Syntax_Syntax.n in
           (match uu___2 with
            | FStarC_Syntax_Syntax.Tm_uvar (u, s) ->
                let uu___3 =
                  let uu___4 =
                    let uu___5 = FStarC_Syntax_Util.ctx_uvar_typ u in
                    FStarC_Syntax_Subst.subst' s uu___5 in
                  FStarC_Syntax_Util.arrow_formals uu___4 in
                (match uu___3 with
                 | (formals, _tres) ->
                     if
                       (FStarC_List.length formals) =
                         (FStarC_List.length args)
                     then t
                     else
                       (let uu___4 =
                          env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                            {
                              FStarC_TypeChecker_Env.solver =
                                (env1.FStarC_TypeChecker_Env.solver);
                              FStarC_TypeChecker_Env.range =
                                (env1.FStarC_TypeChecker_Env.range);
                              FStarC_TypeChecker_Env.curmodule =
                                (env1.FStarC_TypeChecker_Env.curmodule);
                              FStarC_TypeChecker_Env.gamma =
                                (env1.FStarC_TypeChecker_Env.gamma);
                              FStarC_TypeChecker_Env.gamma_sig =
                                (env1.FStarC_TypeChecker_Env.gamma_sig);
                              FStarC_TypeChecker_Env.gamma_cache =
                                (env1.FStarC_TypeChecker_Env.gamma_cache);
                              FStarC_TypeChecker_Env.modules =
                                (env1.FStarC_TypeChecker_Env.modules);
                              FStarC_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStarC_TypeChecker_Env.sigtab =
                                (env1.FStarC_TypeChecker_Env.sigtab);
                              FStarC_TypeChecker_Env.attrtab =
                                (env1.FStarC_TypeChecker_Env.attrtab);
                              FStarC_TypeChecker_Env.instantiate_imp =
                                (env1.FStarC_TypeChecker_Env.instantiate_imp);
                              FStarC_TypeChecker_Env.effects =
                                (env1.FStarC_TypeChecker_Env.effects);
                              FStarC_TypeChecker_Env.generalize =
                                (env1.FStarC_TypeChecker_Env.generalize);
                              FStarC_TypeChecker_Env.letrecs =
                                (env1.FStarC_TypeChecker_Env.letrecs);
                              FStarC_TypeChecker_Env.top_level =
                                (env1.FStarC_TypeChecker_Env.top_level);
                              FStarC_TypeChecker_Env.check_uvars =
                                (env1.FStarC_TypeChecker_Env.check_uvars);
                              FStarC_TypeChecker_Env.use_eq_strict =
                                (env1.FStarC_TypeChecker_Env.use_eq_strict);
                              FStarC_TypeChecker_Env.is_iface =
                                (env1.FStarC_TypeChecker_Env.is_iface);
                              FStarC_TypeChecker_Env.admit = true;
                              FStarC_TypeChecker_Env.phase1 =
                                (env1.FStarC_TypeChecker_Env.phase1);
                              FStarC_TypeChecker_Env.failhard =
                                (env1.FStarC_TypeChecker_Env.failhard);
                              FStarC_TypeChecker_Env.flychecking =
                                (env1.FStarC_TypeChecker_Env.flychecking);
                              FStarC_TypeChecker_Env.uvar_subtyping =
                                (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                              FStarC_TypeChecker_Env.intactics =
                                (env1.FStarC_TypeChecker_Env.intactics);
                              FStarC_TypeChecker_Env.nocoerce =
                                (env1.FStarC_TypeChecker_Env.nocoerce);
                              FStarC_TypeChecker_Env.tc_term =
                                (env1.FStarC_TypeChecker_Env.tc_term);
                              FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                =
                                (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                              FStarC_TypeChecker_Env.universe_of =
                                (env1.FStarC_TypeChecker_Env.universe_of);
                              FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                =
                                (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                              FStarC_TypeChecker_Env.teq_nosmt_force =
                                (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                              FStarC_TypeChecker_Env.subtype_nosmt_force =
                                (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                              FStarC_TypeChecker_Env.qtbl_name_and_index =
                                (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                              FStarC_TypeChecker_Env.normalized_eff_names =
                                (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                              FStarC_TypeChecker_Env.fv_delta_depths =
                                (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                              FStarC_TypeChecker_Env.proof_ns =
                                (env1.FStarC_TypeChecker_Env.proof_ns);
                              FStarC_TypeChecker_Env.synth_hook =
                                (env1.FStarC_TypeChecker_Env.synth_hook);
                              FStarC_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                              FStarC_TypeChecker_Env.splice =
                                (env1.FStarC_TypeChecker_Env.splice);
                              FStarC_TypeChecker_Env.mpreprocess =
                                (env1.FStarC_TypeChecker_Env.mpreprocess);
                              FStarC_TypeChecker_Env.postprocess =
                                (env1.FStarC_TypeChecker_Env.postprocess);
                              FStarC_TypeChecker_Env.identifier_info =
                                (env1.FStarC_TypeChecker_Env.identifier_info);
                              FStarC_TypeChecker_Env.tc_hooks =
                                (env1.FStarC_TypeChecker_Env.tc_hooks);
                              FStarC_TypeChecker_Env.dsenv =
                                (env1.FStarC_TypeChecker_Env.dsenv);
                              FStarC_TypeChecker_Env.nbe =
                                (env1.FStarC_TypeChecker_Env.nbe);
                              FStarC_TypeChecker_Env.strict_args_tab =
                                (env1.FStarC_TypeChecker_Env.strict_args_tab);
                              FStarC_TypeChecker_Env.erasable_types_tab =
                                (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                              FStarC_TypeChecker_Env.enable_defer_to_tac =
                                (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                              FStarC_TypeChecker_Env.unif_allow_ref_guards =
                                (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                              FStarC_TypeChecker_Env.erase_erasable_args =
                                (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                              FStarC_TypeChecker_Env.core_check =
                                (env1.FStarC_TypeChecker_Env.core_check);
                              FStarC_TypeChecker_Env.missing_decl =
                                (env1.FStarC_TypeChecker_Env.missing_decl);
                              FStarC_TypeChecker_Env.iface_todo =
                                (env1.FStarC_TypeChecker_Env.iface_todo);
                              FStarC_TypeChecker_Env.iface_hidden =
                                (env1.FStarC_TypeChecker_Env.iface_hidden);
                              FStarC_TypeChecker_Env.iface_lids =
                                (env1.FStarC_TypeChecker_Env.iface_lids);
                              FStarC_TypeChecker_Env.iface_val_lids =
                                (env1.FStarC_TypeChecker_Env.iface_val_lids)
                            } t true in
                        match uu___4 with
                        | (uu___5, ty, uu___6) ->
                            eta_expand_with_type env1 t ty))
            | uu___3 ->
                let uu___4 =
                  env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                    {
                      FStarC_TypeChecker_Env.solver =
                        (env1.FStarC_TypeChecker_Env.solver);
                      FStarC_TypeChecker_Env.range =
                        (env1.FStarC_TypeChecker_Env.range);
                      FStarC_TypeChecker_Env.curmodule =
                        (env1.FStarC_TypeChecker_Env.curmodule);
                      FStarC_TypeChecker_Env.gamma =
                        (env1.FStarC_TypeChecker_Env.gamma);
                      FStarC_TypeChecker_Env.gamma_sig =
                        (env1.FStarC_TypeChecker_Env.gamma_sig);
                      FStarC_TypeChecker_Env.gamma_cache =
                        (env1.FStarC_TypeChecker_Env.gamma_cache);
                      FStarC_TypeChecker_Env.modules =
                        (env1.FStarC_TypeChecker_Env.modules);
                      FStarC_TypeChecker_Env.expected_typ =
                        FStar_Pervasives_Native.None;
                      FStarC_TypeChecker_Env.sigtab =
                        (env1.FStarC_TypeChecker_Env.sigtab);
                      FStarC_TypeChecker_Env.attrtab =
                        (env1.FStarC_TypeChecker_Env.attrtab);
                      FStarC_TypeChecker_Env.instantiate_imp =
                        (env1.FStarC_TypeChecker_Env.instantiate_imp);
                      FStarC_TypeChecker_Env.effects =
                        (env1.FStarC_TypeChecker_Env.effects);
                      FStarC_TypeChecker_Env.generalize =
                        (env1.FStarC_TypeChecker_Env.generalize);
                      FStarC_TypeChecker_Env.letrecs =
                        (env1.FStarC_TypeChecker_Env.letrecs);
                      FStarC_TypeChecker_Env.top_level =
                        (env1.FStarC_TypeChecker_Env.top_level);
                      FStarC_TypeChecker_Env.check_uvars =
                        (env1.FStarC_TypeChecker_Env.check_uvars);
                      FStarC_TypeChecker_Env.use_eq_strict =
                        (env1.FStarC_TypeChecker_Env.use_eq_strict);
                      FStarC_TypeChecker_Env.is_iface =
                        (env1.FStarC_TypeChecker_Env.is_iface);
                      FStarC_TypeChecker_Env.admit = true;
                      FStarC_TypeChecker_Env.phase1 =
                        (env1.FStarC_TypeChecker_Env.phase1);
                      FStarC_TypeChecker_Env.failhard =
                        (env1.FStarC_TypeChecker_Env.failhard);
                      FStarC_TypeChecker_Env.flychecking =
                        (env1.FStarC_TypeChecker_Env.flychecking);
                      FStarC_TypeChecker_Env.uvar_subtyping =
                        (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                      FStarC_TypeChecker_Env.intactics =
                        (env1.FStarC_TypeChecker_Env.intactics);
                      FStarC_TypeChecker_Env.nocoerce =
                        (env1.FStarC_TypeChecker_Env.nocoerce);
                      FStarC_TypeChecker_Env.tc_term =
                        (env1.FStarC_TypeChecker_Env.tc_term);
                      FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                        (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                      FStarC_TypeChecker_Env.universe_of =
                        (env1.FStarC_TypeChecker_Env.universe_of);
                      FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                        =
                        (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                      FStarC_TypeChecker_Env.teq_nosmt_force =
                        (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                      FStarC_TypeChecker_Env.subtype_nosmt_force =
                        (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                      FStarC_TypeChecker_Env.qtbl_name_and_index =
                        (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                      FStarC_TypeChecker_Env.normalized_eff_names =
                        (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                      FStarC_TypeChecker_Env.fv_delta_depths =
                        (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                      FStarC_TypeChecker_Env.proof_ns =
                        (env1.FStarC_TypeChecker_Env.proof_ns);
                      FStarC_TypeChecker_Env.synth_hook =
                        (env1.FStarC_TypeChecker_Env.synth_hook);
                      FStarC_TypeChecker_Env.try_solve_implicits_hook =
                        (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                      FStarC_TypeChecker_Env.splice =
                        (env1.FStarC_TypeChecker_Env.splice);
                      FStarC_TypeChecker_Env.mpreprocess =
                        (env1.FStarC_TypeChecker_Env.mpreprocess);
                      FStarC_TypeChecker_Env.postprocess =
                        (env1.FStarC_TypeChecker_Env.postprocess);
                      FStarC_TypeChecker_Env.identifier_info =
                        (env1.FStarC_TypeChecker_Env.identifier_info);
                      FStarC_TypeChecker_Env.tc_hooks =
                        (env1.FStarC_TypeChecker_Env.tc_hooks);
                      FStarC_TypeChecker_Env.dsenv =
                        (env1.FStarC_TypeChecker_Env.dsenv);
                      FStarC_TypeChecker_Env.nbe =
                        (env1.FStarC_TypeChecker_Env.nbe);
                      FStarC_TypeChecker_Env.strict_args_tab =
                        (env1.FStarC_TypeChecker_Env.strict_args_tab);
                      FStarC_TypeChecker_Env.erasable_types_tab =
                        (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                      FStarC_TypeChecker_Env.enable_defer_to_tac =
                        (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                      FStarC_TypeChecker_Env.unif_allow_ref_guards =
                        (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                      FStarC_TypeChecker_Env.erase_erasable_args =
                        (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                      FStarC_TypeChecker_Env.core_check =
                        (env1.FStarC_TypeChecker_Env.core_check);
                      FStarC_TypeChecker_Env.missing_decl =
                        (env1.FStarC_TypeChecker_Env.missing_decl);
                      FStarC_TypeChecker_Env.iface_todo =
                        (env1.FStarC_TypeChecker_Env.iface_todo);
                      FStarC_TypeChecker_Env.iface_hidden =
                        (env1.FStarC_TypeChecker_Env.iface_hidden);
                      FStarC_TypeChecker_Env.iface_lids =
                        (env1.FStarC_TypeChecker_Env.iface_lids);
                      FStarC_TypeChecker_Env.iface_val_lids =
                        (env1.FStarC_TypeChecker_Env.iface_val_lids)
                    } t true in
                (match uu___4 with
                 | (uu___5, ty, uu___6) -> eta_expand_with_type env1 t ty)))
let elim_uvars_aux_tc (env1 : FStarC_TypeChecker_Env.env)
  (univ_names : FStarC_Syntax_Syntax.univ_names)
  (binders : FStarC_Syntax_Syntax.binders)
  (tc :
    (FStarC_Syntax_Syntax.typ, FStarC_Syntax_Syntax.comp)
      FStar_Pervasives.either)
  :
  (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.binder Prims.list *
    (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
    FStarC_Syntax_Syntax.comp) FStar_Pervasives.either)=
  let t =
    match (binders, tc) with
    | ([], FStar_Pervasives.Inl t1) -> t1
    | ([], FStar_Pervasives.Inr c) ->
        FStarC_Effect.failwith "Impossible: empty bindes with a comp"
    | (uu___, FStar_Pervasives.Inr c) ->
        FStarC_Syntax_Syntax.mk_Tm_arrow binders c c.FStarC_Syntax_Syntax.pos
    | (uu___, FStar_Pervasives.Inl t1) ->
        let uu___1 = FStarC_Syntax_Syntax.mk_Total t1 in
        FStarC_Syntax_Syntax.mk_Tm_arrow binders uu___1
          t1.FStarC_Syntax_Syntax.pos in
  let uu___ = FStarC_Syntax_Subst.open_univ_vars univ_names t in
  match uu___ with
  | (univ_names1, t1) ->
      let t2 = remove_uvar_solutions env1 t1 in
      let t3 = FStarC_Syntax_Subst.close_univ_vars univ_names1 t2 in
      let uu___1 =
        match binders with
        | [] -> ([], (FStar_Pervasives.Inl t3))
        | uu___2 ->
            let n = FStarC_List.length binders in
            let rec unpack n1 t4 =
              let uu___3 =
                let uu___4 = FStarC_Syntax_Subst.compress t4 in
                uu___4.FStarC_Syntax_Syntax.n in
              match uu___3 with
              | FStarC_Syntax_Syntax.Tm_arrow
                  { FStarC_Syntax_Syntax.b1 = b;
                    FStarC_Syntax_Syntax.comp = c;_}
                  ->
                  if n1 <= Prims.int_one
                  then ([b], c)
                  else
                    (let uu___4 =
                       unpack (n1 - Prims.int_one)
                         (FStarC_Syntax_Util.comp_result c) in
                     match uu___4 with | (bs, c1) -> ((b :: bs), c1))
              | uu___4 ->
                  FStarC_Effect.failwith
                    "Impossible: elim_uvars_aux_tc expected an arrow" in
            let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Syntax_Subst.compress t3 in
                uu___5.FStarC_Syntax_Syntax.n in
              (uu___4, tc) in
            (match uu___3 with
             | (FStarC_Syntax_Syntax.Tm_arrow uu___4, FStar_Pervasives.Inr
                uu___5) ->
                 let uu___6 = unpack n t3 in
                 (match uu___6 with
                  | (binders1, c) -> (binders1, (FStar_Pervasives.Inr c)))
             | (FStarC_Syntax_Syntax.Tm_arrow uu___4, FStar_Pervasives.Inl
                uu___5) ->
                 let uu___6 = unpack n t3 in
                 (match uu___6 with
                  | (binders1, c) ->
                      (binders1,
                        (FStar_Pervasives.Inl
                           (FStarC_Syntax_Util.comp_result c))))
             | (uu___4, FStar_Pervasives.Inl uu___5) ->
                 ([], (FStar_Pervasives.Inl t3))
             | uu___4 -> FStarC_Effect.failwith "Impossible") in
      (match uu___1 with | (binders1, tc1) -> (univ_names1, binders1, tc1))
let elim_uvars_aux_t (env1 : FStarC_TypeChecker_Env.env)
  (univ_names : FStarC_Syntax_Syntax.univ_names)
  (binders : FStarC_Syntax_Syntax.binders) (t : FStarC_Syntax_Syntax.typ) :
  (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.binder Prims.list *
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)=
  let uu___ =
    elim_uvars_aux_tc env1 univ_names binders (FStar_Pervasives.Inl t) in
  match uu___ with
  | (univ_names1, binders1, tc) ->
      (univ_names1, binders1,
        ((match tc with | FStar_Pervasives.Inl v -> v)))
let elim_uvars_aux_c (env1 : FStarC_TypeChecker_Env.env)
  (univ_names : FStarC_Syntax_Syntax.univ_names)
  (binders : FStarC_Syntax_Syntax.binders) (c : FStarC_Syntax_Syntax.comp) :
  (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.binder Prims.list *
    FStarC_Syntax_Syntax.comp)=
  let uu___ =
    elim_uvars_aux_tc env1 univ_names binders (FStar_Pervasives.Inr c) in
  match uu___ with
  | (univ_names1, binders1, tc) ->
      (univ_names1, binders1,
        ((match tc with | FStar_Pervasives.Inr v -> v)))
let rec elim_uvars (env1 : FStarC_TypeChecker_Env.env)
  (s : FStarC_Syntax_Syntax.sigelt) : FStarC_Syntax_Syntax.sigelt=
  let sigattrs =
    let uu___ =
      FStarC_List.map (elim_uvars_aux_t env1 [] [])
        s.FStarC_Syntax_Syntax.sigattrs in
    FStarC_List.map FStar_Pervasives_Native.__proj__Mktuple3__item___3 uu___ in
  let s1 =
    {
      FStarC_Syntax_Syntax.sigel = (s.FStarC_Syntax_Syntax.sigel);
      FStarC_Syntax_Syntax.sigrng = (s.FStarC_Syntax_Syntax.sigrng);
      FStarC_Syntax_Syntax.sigquals = (s.FStarC_Syntax_Syntax.sigquals);
      FStarC_Syntax_Syntax.sigmeta = (s.FStarC_Syntax_Syntax.sigmeta);
      FStarC_Syntax_Syntax.sigattrs = sigattrs;
      FStarC_Syntax_Syntax.sigopens_and_abbrevs =
        (s.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
      FStarC_Syntax_Syntax.sigopts = (s.FStarC_Syntax_Syntax.sigopts)
    } in
  match s1.FStarC_Syntax_Syntax.sigel with
  | FStarC_Syntax_Syntax.Sig_inductive_typ
      { FStarC_Syntax_Syntax.lid = lid; FStarC_Syntax_Syntax.us = univ_names;
        FStarC_Syntax_Syntax.params = binders;
        FStarC_Syntax_Syntax.num_uniform_params = num_uniform;
        FStarC_Syntax_Syntax.t = typ; FStarC_Syntax_Syntax.mutuals = lids;
        FStarC_Syntax_Syntax.ds = lids';
        FStarC_Syntax_Syntax.injective_type_params = injective_type_params;_}
      ->
      let uu___ = elim_uvars_aux_t env1 univ_names binders typ in
      (match uu___ with
       | (univ_names1, binders1, typ1) ->
           {
             FStarC_Syntax_Syntax.sigel =
               (FStarC_Syntax_Syntax.Sig_inductive_typ
                  {
                    FStarC_Syntax_Syntax.lid = lid;
                    FStarC_Syntax_Syntax.us = univ_names1;
                    FStarC_Syntax_Syntax.params = binders1;
                    FStarC_Syntax_Syntax.num_uniform_params = num_uniform;
                    FStarC_Syntax_Syntax.t = typ1;
                    FStarC_Syntax_Syntax.mutuals = lids;
                    FStarC_Syntax_Syntax.ds = lids';
                    FStarC_Syntax_Syntax.injective_type_params =
                      injective_type_params
                  });
             FStarC_Syntax_Syntax.sigrng = (s1.FStarC_Syntax_Syntax.sigrng);
             FStarC_Syntax_Syntax.sigquals =
               (s1.FStarC_Syntax_Syntax.sigquals);
             FStarC_Syntax_Syntax.sigmeta = (s1.FStarC_Syntax_Syntax.sigmeta);
             FStarC_Syntax_Syntax.sigattrs =
               (s1.FStarC_Syntax_Syntax.sigattrs);
             FStarC_Syntax_Syntax.sigopens_and_abbrevs =
               (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
             FStarC_Syntax_Syntax.sigopts = (s1.FStarC_Syntax_Syntax.sigopts)
           })
  | FStarC_Syntax_Syntax.Sig_bundle
      { FStarC_Syntax_Syntax.ses = sigs; FStarC_Syntax_Syntax.lids = lids;_}
      ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map (elim_uvars env1) sigs in
          {
            FStarC_Syntax_Syntax.ses = uu___2;
            FStarC_Syntax_Syntax.lids = lids
          } in
        FStarC_Syntax_Syntax.Sig_bundle uu___1 in
      {
        FStarC_Syntax_Syntax.sigel = uu___;
        FStarC_Syntax_Syntax.sigrng = (s1.FStarC_Syntax_Syntax.sigrng);
        FStarC_Syntax_Syntax.sigquals = (s1.FStarC_Syntax_Syntax.sigquals);
        FStarC_Syntax_Syntax.sigmeta = (s1.FStarC_Syntax_Syntax.sigmeta);
        FStarC_Syntax_Syntax.sigattrs = (s1.FStarC_Syntax_Syntax.sigattrs);
        FStarC_Syntax_Syntax.sigopens_and_abbrevs =
          (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
        FStarC_Syntax_Syntax.sigopts = (s1.FStarC_Syntax_Syntax.sigopts)
      }
  | FStarC_Syntax_Syntax.Sig_datacon
      { FStarC_Syntax_Syntax.lid1 = lid;
        FStarC_Syntax_Syntax.us1 = univ_names; FStarC_Syntax_Syntax.t1 = typ;
        FStarC_Syntax_Syntax.ty_lid = lident;
        FStarC_Syntax_Syntax.num_ty_params = i;
        FStarC_Syntax_Syntax.mutuals1 = lids;
        FStarC_Syntax_Syntax.injective_type_params1 = injective_type_params;
        FStarC_Syntax_Syntax.proj_disc_lids = proj_disc_lids;_}
      ->
      let uu___ = elim_uvars_aux_t env1 univ_names [] typ in
      (match uu___ with
       | (univ_names1, uu___1, typ1) ->
           {
             FStarC_Syntax_Syntax.sigel =
               (FStarC_Syntax_Syntax.Sig_datacon
                  {
                    FStarC_Syntax_Syntax.lid1 = lid;
                    FStarC_Syntax_Syntax.us1 = univ_names1;
                    FStarC_Syntax_Syntax.t1 = typ1;
                    FStarC_Syntax_Syntax.ty_lid = lident;
                    FStarC_Syntax_Syntax.num_ty_params = i;
                    FStarC_Syntax_Syntax.mutuals1 = lids;
                    FStarC_Syntax_Syntax.injective_type_params1 =
                      injective_type_params;
                    FStarC_Syntax_Syntax.proj_disc_lids = proj_disc_lids
                  });
             FStarC_Syntax_Syntax.sigrng = (s1.FStarC_Syntax_Syntax.sigrng);
             FStarC_Syntax_Syntax.sigquals =
               (s1.FStarC_Syntax_Syntax.sigquals);
             FStarC_Syntax_Syntax.sigmeta = (s1.FStarC_Syntax_Syntax.sigmeta);
             FStarC_Syntax_Syntax.sigattrs =
               (s1.FStarC_Syntax_Syntax.sigattrs);
             FStarC_Syntax_Syntax.sigopens_and_abbrevs =
               (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
             FStarC_Syntax_Syntax.sigopts = (s1.FStarC_Syntax_Syntax.sigopts)
           })
  | FStarC_Syntax_Syntax.Sig_declare_typ
      { FStarC_Syntax_Syntax.lid2 = lid;
        FStarC_Syntax_Syntax.us2 = univ_names;
        FStarC_Syntax_Syntax.t2 = typ;_}
      ->
      let uu___ = elim_uvars_aux_t env1 univ_names [] typ in
      (match uu___ with
       | (univ_names1, uu___1, typ1) ->
           {
             FStarC_Syntax_Syntax.sigel =
               (FStarC_Syntax_Syntax.Sig_declare_typ
                  {
                    FStarC_Syntax_Syntax.lid2 = lid;
                    FStarC_Syntax_Syntax.us2 = univ_names1;
                    FStarC_Syntax_Syntax.t2 = typ1
                  });
             FStarC_Syntax_Syntax.sigrng = (s1.FStarC_Syntax_Syntax.sigrng);
             FStarC_Syntax_Syntax.sigquals =
               (s1.FStarC_Syntax_Syntax.sigquals);
             FStarC_Syntax_Syntax.sigmeta = (s1.FStarC_Syntax_Syntax.sigmeta);
             FStarC_Syntax_Syntax.sigattrs =
               (s1.FStarC_Syntax_Syntax.sigattrs);
             FStarC_Syntax_Syntax.sigopens_and_abbrevs =
               (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
             FStarC_Syntax_Syntax.sigopts = (s1.FStarC_Syntax_Syntax.sigopts)
           })
  | FStarC_Syntax_Syntax.Sig_let
      { FStarC_Syntax_Syntax.lbs1 = (b, lbs);
        FStarC_Syntax_Syntax.lids1 = lids;_}
      ->
      let lbs1 =
        FStarC_List.map
          (fun lb ->
             let uu___ =
               FStarC_Syntax_Subst.univ_var_opening
                 lb.FStarC_Syntax_Syntax.lbunivs in
             match uu___ with
             | (opening, lbunivs) ->
                 let elim t =
                   let uu___1 =
                     let uu___2 = FStarC_Syntax_Subst.subst opening t in
                     remove_uvar_solutions env1 uu___2 in
                   FStarC_Syntax_Subst.close_univ_vars lbunivs uu___1 in
                 let lbtyp = elim lb.FStarC_Syntax_Syntax.lbtyp in
                 let lbdef = elim lb.FStarC_Syntax_Syntax.lbdef in
                 {
                   FStarC_Syntax_Syntax.lbname =
                     (lb.FStarC_Syntax_Syntax.lbname);
                   FStarC_Syntax_Syntax.lbunivs = lbunivs;
                   FStarC_Syntax_Syntax.lbtyp = lbtyp;
                   FStarC_Syntax_Syntax.lbeff =
                     (lb.FStarC_Syntax_Syntax.lbeff);
                   FStarC_Syntax_Syntax.lbdef = lbdef;
                   FStarC_Syntax_Syntax.lbattrs =
                     (lb.FStarC_Syntax_Syntax.lbattrs);
                   FStarC_Syntax_Syntax.lbpos =
                     (lb.FStarC_Syntax_Syntax.lbpos)
                 }) lbs in
      {
        FStarC_Syntax_Syntax.sigel =
          (FStarC_Syntax_Syntax.Sig_let
             {
               FStarC_Syntax_Syntax.lbs1 = (b, lbs1);
               FStarC_Syntax_Syntax.lids1 = lids
             });
        FStarC_Syntax_Syntax.sigrng = (s1.FStarC_Syntax_Syntax.sigrng);
        FStarC_Syntax_Syntax.sigquals = (s1.FStarC_Syntax_Syntax.sigquals);
        FStarC_Syntax_Syntax.sigmeta = (s1.FStarC_Syntax_Syntax.sigmeta);
        FStarC_Syntax_Syntax.sigattrs = (s1.FStarC_Syntax_Syntax.sigattrs);
        FStarC_Syntax_Syntax.sigopens_and_abbrevs =
          (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
        FStarC_Syntax_Syntax.sigopts = (s1.FStarC_Syntax_Syntax.sigopts)
      }
  | FStarC_Syntax_Syntax.Sig_assume
      { FStarC_Syntax_Syntax.lid3 = l; FStarC_Syntax_Syntax.us3 = us;
        FStarC_Syntax_Syntax.phi1 = t;_}
      ->
      let uu___ = elim_uvars_aux_t env1 us [] t in
      (match uu___ with
       | (us1, uu___1, t1) ->
           {
             FStarC_Syntax_Syntax.sigel =
               (FStarC_Syntax_Syntax.Sig_assume
                  {
                    FStarC_Syntax_Syntax.lid3 = l;
                    FStarC_Syntax_Syntax.us3 = us1;
                    FStarC_Syntax_Syntax.phi1 = t1
                  });
             FStarC_Syntax_Syntax.sigrng = (s1.FStarC_Syntax_Syntax.sigrng);
             FStarC_Syntax_Syntax.sigquals =
               (s1.FStarC_Syntax_Syntax.sigquals);
             FStarC_Syntax_Syntax.sigmeta = (s1.FStarC_Syntax_Syntax.sigmeta);
             FStarC_Syntax_Syntax.sigattrs =
               (s1.FStarC_Syntax_Syntax.sigattrs);
             FStarC_Syntax_Syntax.sigopens_and_abbrevs =
               (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
             FStarC_Syntax_Syntax.sigopts = (s1.FStarC_Syntax_Syntax.sigopts)
           })
  | FStarC_Syntax_Syntax.Sig_new_effect ed -> s1
  | FStarC_Syntax_Syntax.Sig_sub_effect sub_eff -> s1
  | FStarC_Syntax_Syntax.Sig_effect_abbrev
      { FStarC_Syntax_Syntax.lid4 = lid;
        FStarC_Syntax_Syntax.us4 = univ_names;
        FStarC_Syntax_Syntax.bs = binders; FStarC_Syntax_Syntax.comp1 = comp;
        FStarC_Syntax_Syntax.cflags = flags;_}
      ->
      let uu___ = elim_uvars_aux_c env1 univ_names binders comp in
      (match uu___ with
       | (univ_names1, binders1, comp1) ->
           {
             FStarC_Syntax_Syntax.sigel =
               (FStarC_Syntax_Syntax.Sig_effect_abbrev
                  {
                    FStarC_Syntax_Syntax.lid4 = lid;
                    FStarC_Syntax_Syntax.us4 = univ_names1;
                    FStarC_Syntax_Syntax.bs = binders1;
                    FStarC_Syntax_Syntax.comp1 = comp1;
                    FStarC_Syntax_Syntax.cflags = flags
                  });
             FStarC_Syntax_Syntax.sigrng = (s1.FStarC_Syntax_Syntax.sigrng);
             FStarC_Syntax_Syntax.sigquals =
               (s1.FStarC_Syntax_Syntax.sigquals);
             FStarC_Syntax_Syntax.sigmeta = (s1.FStarC_Syntax_Syntax.sigmeta);
             FStarC_Syntax_Syntax.sigattrs =
               (s1.FStarC_Syntax_Syntax.sigattrs);
             FStarC_Syntax_Syntax.sigopens_and_abbrevs =
               (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
             FStarC_Syntax_Syntax.sigopts = (s1.FStarC_Syntax_Syntax.sigopts)
           })
  | FStarC_Syntax_Syntax.Sig_pragma uu___ -> s1
  | FStarC_Syntax_Syntax.Sig_fail uu___ -> s1
  | FStarC_Syntax_Syntax.Sig_splice uu___ -> s1
let erase_universes (env1 : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  normalize
    [FStarC_TypeChecker_Env.EraseUniverses;
    FStarC_TypeChecker_Env.AllowUnboundUniverses] env1 t
let unfold_head_once (env1 : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let aux f us args =
    let uu___ =
      FStarC_TypeChecker_Env.lookup_nonrec_definition
        [FStarC_TypeChecker_Env.Unfold FStarC_Syntax_Syntax.delta_constant]
        env1 f.FStarC_Syntax_Syntax.fv_name in
    match uu___ with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some head_def_ts ->
        let uu___1 = FStarC_TypeChecker_Env.inst_tscheme_with head_def_ts us in
        (match uu___1 with
         | (uu___2, head_def) ->
             let t' =
               FStarC_Syntax_Syntax.mk_Tm_app head_def args
                 t.FStarC_Syntax_Syntax.pos in
             let t'1 =
               normalize
                 [FStarC_TypeChecker_Env.Beta; FStarC_TypeChecker_Env.Iota]
                 env1 t' in
             FStar_Pervasives_Native.Some t'1) in
  let uu___ = FStarC_Syntax_Util.head_and_args_full t in
  match uu___ with
  | (head, args) ->
      let uu___1 =
        let uu___2 = FStarC_Syntax_Subst.compress head in
        uu___2.FStarC_Syntax_Syntax.n in
      (match uu___1 with
       | FStarC_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
       | FStarC_Syntax_Syntax.Tm_uinst
           ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
              FStarC_Syntax_Syntax.pos = uu___2;
              FStarC_Syntax_Syntax.hash_code = uu___3;_},
            us)
           -> aux fv us args
       | uu___2 -> FStar_Pervasives_Native.None)
let get_n_binders' (env1 : FStarC_TypeChecker_Env.env)
  (steps : FStarC_TypeChecker_Env.step Prims.list) (n : Prims.int)
  (t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.binder Prims.list * FStarC_Syntax_Syntax.comp)=
  let rec aux retry n1 t1 =
    let uu___ = FStarC_Syntax_Util.arrow_formals_comp t1 in
    match uu___ with
    | (bs, c) ->
        let len = FStarC_List.length bs in
        (match (bs, c) with
         | ([], uu___1) when retry ->
             let uu___2 = unfold_whnf' steps env1 t1 in aux false n1 uu___2
         | ([], uu___1) when Prims.not retry -> (bs, c)
         | (bs1, c1) when len = n1 -> (bs1, c1)
         | (bs1, c1) when len > n1 ->
             let uu___1 = FStarC_List.splitAt n1 bs1 in
             (match uu___1 with
              | (bs_l, bs_r) ->
                  let uu___2 =
                    let uu___3 = FStarC_Syntax_Util.arrow bs_r c1 in
                    FStarC_Syntax_Syntax.mk_Total uu___3 in
                  (bs_l, uu___2))
         | (bs1, c1) when
             let uu___1 =
               if len < n1
               then FStarC_Syntax_Util.is_total_comp c1
               else false in
             if uu___1
             then
               let uu___2 = FStarC_Syntax_Util.has_decreases c1 in
               Prims.not uu___2
             else false ->
             let uu___1 =
               aux true (n1 - len) (FStarC_Syntax_Util.comp_result c1) in
             (match uu___1 with
              | (bs', c') -> ((FStarC_List.op_At bs1 bs'), c'))
         | (bs1, c1) -> (bs1, c1)) in
  aux true n t
let get_n_binders (env1 : FStarC_TypeChecker_Env.env) (n : Prims.int)
  (t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.binder Prims.list * FStarC_Syntax_Syntax.comp)=
  get_n_binders' env1 [] n t
let uu___0 : unit=
  FStarC_Effect.op_Colon_Equals __get_n_binders get_n_binders'
let maybe_unfold_head_fv (env1 : FStarC_TypeChecker_Env.env)
  (head : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let fv_us_opt =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress head in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_uinst
        ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
           FStarC_Syntax_Syntax.pos = uu___1;
           FStarC_Syntax_Syntax.hash_code = uu___2;_},
         us)
        -> FStar_Pervasives_Native.Some (fv, us)
    | FStarC_Syntax_Syntax.Tm_fvar fv ->
        FStar_Pervasives_Native.Some (fv, [])
    | uu___1 -> FStar_Pervasives_Native.None in
  match fv_us_opt with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (fv, us) ->
      let uu___ =
        FStarC_TypeChecker_Env.lookup_nonrec_definition
          [FStarC_TypeChecker_Env.Unfold FStarC_Syntax_Syntax.delta_constant]
          env1 fv.FStarC_Syntax_Syntax.fv_name in
      (match uu___ with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (us_formals, defn) ->
           let subst = FStarC_TypeChecker_Env.mk_univ_subst us_formals us in
           let uu___1 = FStarC_Syntax_Subst.subst subst defn in
           FStar_Pervasives_Native.Some uu___1)
let disc_proj_scrutinee_index (env1 : FStarC_TypeChecker_Env.env)
  (head : FStarC_Syntax_Syntax.term) (n_args : Prims.int) :
  Prims.int FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = FStarC_Syntax_Util.un_uinst head in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_fvar fv ->
      let uu___1 =
        FStarC_TypeChecker_Env.disc_proj_info env1
          fv.FStarC_Syntax_Syntax.fv_name in
      (match uu___1 with
       | FStar_Pervasives_Native.Some (uu___2, n_indexed, uu___3) when
           n_args > n_indexed -> FStar_Pervasives_Native.Some n_indexed
       | uu___2 -> FStar_Pervasives_Native.None)
  | uu___1 -> FStar_Pervasives_Native.None
let rec maybe_unfold_aux (env1 : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = FStarC_Syntax_Subst.compress t in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_match
      { FStarC_Syntax_Syntax.scrutinee = t0;
        FStarC_Syntax_Syntax.ret_opt = ret_opt;
        FStarC_Syntax_Syntax.brs = brs;
        FStarC_Syntax_Syntax.rc_opt1 = rc_opt;_}
      ->
      let uu___1 = maybe_unfold_aux env1 t0 in
      FStarC_Option.map
        (fun t01 ->
           FStarC_Syntax_Syntax.mk
             (FStarC_Syntax_Syntax.Tm_match
                {
                  FStarC_Syntax_Syntax.scrutinee = t01;
                  FStarC_Syntax_Syntax.ret_opt = ret_opt;
                  FStarC_Syntax_Syntax.brs = brs;
                  FStarC_Syntax_Syntax.rc_opt1 = rc_opt
                }) t.FStarC_Syntax_Syntax.pos) uu___1
  | FStarC_Syntax_Syntax.Tm_fvar uu___1 -> maybe_unfold_head_fv env1 t
  | FStarC_Syntax_Syntax.Tm_uinst uu___1 -> maybe_unfold_head_fv env1 t
  | uu___1 ->
      let uu___2 = FStarC_Syntax_Util.leftmost_head_and_args t in
      (match uu___2 with
       | (head, args) ->
           if args = []
           then maybe_unfold_head_fv env1 head
           else
             (let uu___3 = maybe_unfold_aux env1 head in
              match uu___3 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu___4 =
                    FStarC_Syntax_Syntax.mk_Tm_app head1 args
                      t.FStarC_Syntax_Syntax.pos in
                  FStar_Pervasives_Native.Some uu___4
              | FStar_Pervasives_Native.None ->
                  let uu___4 =
                    disc_proj_scrutinee_index env1 head
                      (FStarC_List.length args) in
                  (match uu___4 with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some i ->
                       let uu___5 = FStarC_List.nth args i in
                       (match uu___5 with
                        | (scrutinee, aq) ->
                            let uu___6 = maybe_unfold_aux env1 scrutinee in
                            (match uu___6 with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some scrutinee1 ->
                                 let args1 =
                                   FStarC_List.mapi
                                     (fun j a ->
                                        if j = i then (scrutinee1, aq) else a)
                                     args in
                                 let uu___7 =
                                   FStarC_Syntax_Syntax.mk_Tm_app head args1
                                     t.FStarC_Syntax_Syntax.pos in
                                 FStar_Pervasives_Native.Some uu___7)))))
let maybe_unfold_head (env1 : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ = maybe_unfold_aux env1 t in
  FStarC_Option.map
    (normalize
       [FStarC_TypeChecker_Env.Beta;
       FStarC_TypeChecker_Env.Iota;
       FStarC_TypeChecker_Env.Weak;
       FStarC_TypeChecker_Env.HNF] env1) uu___
