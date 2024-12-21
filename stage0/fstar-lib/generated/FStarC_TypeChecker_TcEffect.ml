open Prims
let (dbg : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "ED"
let (dbg_LayeredEffectsTc : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "LayeredEffectsTc"
let (dmff_cps_and_elaborate :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.eff_decl ->
      (FStarC_Syntax_Syntax.sigelt Prims.list * FStarC_Syntax_Syntax.eff_decl
        * FStarC_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  = fun env -> fun ed -> FStarC_TypeChecker_DMFF.cps_and_elaborate env ed
let (check_and_gen :
  FStarC_TypeChecker_Env.env ->
    Prims.string ->
      Prims.string ->
        Prims.int ->
          (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.term) ->
            (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.term *
              FStarC_Syntax_Syntax.typ))
  =
  fun env ->
    fun eff_name ->
      fun comb ->
        fun n ->
          fun uu___ ->
            match uu___ with
            | (us, t) ->
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        FStarC_Class_Show.show
                          (FStarC_Class_Show.show_tuple2
                             (FStarC_Class_Show.show_list
                                FStarC_Ident.showable_ident)
                             FStarC_Syntax_Print.showable_term) (us, t) in
                      Prims.strcat " = " uu___4 in
                    Prims.strcat comb uu___3 in
                  Prims.strcat "While checking combinator " uu___2 in
                FStarC_Errors.with_ctx uu___1
                  (fun uu___2 ->
                     let uu___3 = FStarC_Syntax_Subst.open_univ_vars us t in
                     match uu___3 with
                     | (us1, t1) ->
                         let uu___4 =
                           let uu___5 =
                             let uu___6 =
                               FStarC_TypeChecker_Env.push_univ_vars env us1 in
                             FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               uu___6 t1 in
                           match uu___5 with
                           | (t2, lc, g) ->
                               (FStarC_TypeChecker_Rel.force_trivial_guard
                                  env g;
                                (t2, (lc.FStarC_TypeChecker_Common.res_typ))) in
                         (match uu___4 with
                          | (t2, ty) ->
                              let uu___5 =
                                FStarC_TypeChecker_Generalize.generalize_universes
                                  env t2 in
                              (match uu___5 with
                               | (g_us, t3) ->
                                   let ty1 =
                                     FStarC_Syntax_Subst.close_univ_vars g_us
                                       ty in
                                   (if
                                      (FStarC_Compiler_List.length g_us) <> n
                                    then
                                      (let error =
                                         let uu___6 =
                                           FStarC_Compiler_Util.string_of_int
                                             n in
                                         let uu___7 =
                                           FStarC_Compiler_Util.string_of_int
                                             (FStarC_Compiler_List.length
                                                g_us) in
                                         let uu___8 =
                                           FStarC_Syntax_Print.tscheme_to_string
                                             (g_us, t3) in
                                         FStarC_Compiler_Util.format5
                                           "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
                                           eff_name comb uu___6 uu___7 uu___8 in
                                       FStarC_Errors.raise_error
                                         (FStarC_Syntax_Syntax.has_range_syntax
                                            ()) t3
                                         FStarC_Errors_Codes.Fatal_MismatchUniversePolymorphic
                                         ()
                                         (Obj.magic
                                            FStarC_Errors_Msg.is_error_message_string)
                                         (Obj.magic error);
                                       (match us1 with
                                        | [] -> ()
                                        | uu___7 ->
                                            let uu___8 =
                                              ((FStarC_Compiler_List.length
                                                  us1)
                                                 =
                                                 (FStarC_Compiler_List.length
                                                    g_us))
                                                &&
                                                (FStarC_Compiler_List.forall2
                                                   (fun u1 ->
                                                      fun u2 ->
                                                        let uu___9 =
                                                          FStarC_Syntax_Syntax.order_univ_name
                                                            u1 u2 in
                                                        uu___9 =
                                                          Prims.int_zero) us1
                                                   g_us) in
                                            if uu___8
                                            then ()
                                            else
                                              (let uu___10 =
                                                 let uu___11 =
                                                   FStarC_Class_Show.show
                                                     (FStarC_Class_Show.show_list
                                                        FStarC_Ident.showable_ident)
                                                     us1 in
                                                 let uu___12 =
                                                   FStarC_Class_Show.show
                                                     (FStarC_Class_Show.show_list
                                                        FStarC_Ident.showable_ident)
                                                     g_us in
                                                 FStarC_Compiler_Util.format4
                                                   "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                   eff_name comb uu___11
                                                   uu___12 in
                                               FStarC_Errors.raise_error
                                                 (FStarC_Syntax_Syntax.has_range_syntax
                                                    ()) t3
                                                 FStarC_Errors_Codes.Fatal_UnexpectedNumberOfUniverse
                                                 ()
                                                 (Obj.magic
                                                    FStarC_Errors_Msg.is_error_message_string)
                                                 (Obj.magic uu___10))))
                                    else ();
                                    (g_us, t3, ty1)))))
let (pure_wp_uvar :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ ->
      Prims.string ->
        FStarC_Compiler_Range_Type.range ->
          (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun t ->
      fun reason ->
        fun r ->
          let pure_wp_t =
            let pure_wp_ts =
              let uu___ =
                FStarC_TypeChecker_Env.lookup_definition
                  [FStarC_TypeChecker_Env.NoDelta] env
                  FStarC_Parser_Const.pure_wp_lid in
              FStarC_Compiler_Util.must uu___ in
            let uu___ = FStarC_TypeChecker_Env.inst_tscheme pure_wp_ts in
            match uu___ with
            | (uu___1, pure_wp_t1) ->
                let uu___2 =
                  let uu___3 = FStarC_Syntax_Syntax.as_arg t in [uu___3] in
                FStarC_Syntax_Syntax.mk_Tm_app pure_wp_t1 uu___2 r in
          let uu___ =
            FStarC_TypeChecker_Env.new_implicit_var_aux reason r env
              pure_wp_t FStarC_Syntax_Syntax.Strict
              FStar_Pervasives_Native.None false in
          match uu___ with
          | (pure_wp_uvar1, uu___1, guard_wp) -> (pure_wp_uvar1, guard_wp)
let op_let_Question :
  'a 'b .
    'a FStar_Pervasives_Native.option ->
      ('a -> 'b FStar_Pervasives_Native.option) ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun g ->
      match f with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some x -> g x
let (mteq :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        try
          (fun uu___ ->
             match () with
             | () -> FStarC_TypeChecker_Rel.teq_nosmt_force env t1 t2) ()
        with | uu___ -> false
let (eq_binders :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.binders ->
        FStarC_Syntax_Syntax.indexed_effect_binder_kind Prims.list
          FStar_Pervasives_Native.option)
  =
  fun env ->
    fun bs1 ->
      fun bs2 ->
        let uu___ =
          let uu___1 =
            FStarC_Compiler_List.fold_left2
              (fun uu___2 ->
                 fun b1 ->
                   fun b2 ->
                     match uu___2 with
                     | (b, ss) ->
                         let uu___3 =
                           b &&
                             (let uu___4 =
                                FStarC_Syntax_Subst.subst ss
                                  (b1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                              mteq env uu___4
                                (b2.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort) in
                         let uu___4 =
                           let uu___5 =
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   FStarC_Syntax_Syntax.bv_to_name
                                     b2.FStarC_Syntax_Syntax.binder_bv in
                                 ((b1.FStarC_Syntax_Syntax.binder_bv),
                                   uu___8) in
                               FStarC_Syntax_Syntax.NT uu___7 in
                             [uu___6] in
                           FStarC_Compiler_List.op_At ss uu___5 in
                         (uu___3, uu___4)) (true, []) bs1 bs2 in
          FStar_Pervasives_Native.fst uu___1 in
        if uu___
        then
          let uu___1 =
            FStarC_Compiler_List.map
              (fun uu___2 -> FStarC_Syntax_Syntax.Substitutive_binder) bs1 in
          FStar_Pervasives_Native.Some uu___1
        else FStar_Pervasives_Native.None
let (log_ad_hoc_combinator_warning :
  Prims.string -> FStarC_Compiler_Range_Type.range -> unit) =
  fun comb_name ->
    fun r ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Compiler_Util.format1
              "Combinator %s is not a substitutive indexed effect combinator, it is better to make it one if possible for better performance and ease of use"
              comb_name in
          FStarC_Errors_Msg.text uu___2 in
        [uu___1] in
      FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range r
        FStarC_Errors_Codes.Warning_Adhoc_IndexedEffect_Combinator ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic uu___)
let (bind_combinator_kind :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Ident.lident ->
        FStarC_Ident.lident ->
          FStarC_Syntax_Syntax.tscheme ->
            FStarC_Syntax_Syntax.tscheme ->
              FStarC_Syntax_Syntax.tscheme ->
                FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option
                  ->
                  FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option
                    ->
                    FStarC_Syntax_Syntax.tscheme
                      FStar_Pervasives_Native.option ->
                      FStarC_Syntax_Syntax.univ_names ->
                        FStarC_Syntax_Syntax.typ ->
                          Prims.int ->
                            Prims.bool ->
                              FStarC_Syntax_Syntax.indexed_effect_binder_kind
                                Prims.list FStar_Pervasives_Native.option)
  =
  fun env ->
    fun m_eff_name ->
      fun n_eff_name ->
        fun p_eff_name ->
          fun m_sig_ts ->
            fun n_sig_ts ->
              fun p_sig_ts ->
                fun m_repr_ts ->
                  fun n_repr_ts ->
                    fun p_repr_ts ->
                      fun bind_us ->
                        fun k ->
                          fun num_effect_params ->
                            fun has_range_binders ->
                              let debug s =
                                let uu___ =
                                  (FStarC_Compiler_Debug.medium ()) ||
                                    (FStarC_Compiler_Effect.op_Bang
                                       dbg_LayeredEffectsTc) in
                                if uu___
                                then FStarC_Compiler_Util.print1 "%s\n" s
                                else () in
                              (let uu___1 =
                                 let uu___2 =
                                   FStarC_Compiler_Util.string_of_int
                                     num_effect_params in
                                 FStarC_Compiler_Util.format1
                                   "Checking bind combinator kind with %s effect parameters"
                                   uu___2 in
                               debug uu___1);
                              (let uu___1 = bind_us in
                               match uu___1 with
                               | u_a::u_b::[] ->
                                   let uu___2 =
                                     let uu___3 =
                                       FStarC_Syntax_Util.arrow_formals k in
                                     FStar_Pervasives_Native.fst uu___3 in
                                   (match uu___2 with
                                    | a_b::b_b::rest_bs ->
                                        let uu___3 =
                                          if
                                            num_effect_params =
                                              Prims.int_zero
                                          then
                                            FStar_Pervasives_Native.Some
                                              ([], [], rest_bs)
                                          else
                                            (let uu___5 =
                                               FStarC_TypeChecker_Env.inst_tscheme_with
                                                 m_sig_ts
                                                 [FStarC_Syntax_Syntax.U_name
                                                    u_a] in
                                             match uu___5 with
                                             | (uu___6, sig1) ->
                                                 let sig_bs =
                                                   let uu___7 =
                                                     let uu___8 =
                                                       FStarC_Syntax_Util.arrow_formals
                                                         sig1 in
                                                     FStar_Pervasives_Native.fst
                                                       uu___8 in
                                                   FStarC_Compiler_List.tl
                                                     uu___7 in
                                                 let uu___7 =
                                                   if
                                                     (FStarC_Compiler_List.length
                                                        sig_bs)
                                                       < num_effect_params
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (let uu___9 =
                                                        let uu___10 =
                                                          FStarC_Compiler_List.splitAt
                                                            num_effect_params
                                                            sig_bs in
                                                        FStar_Pervasives_Native.fst
                                                          uu___10 in
                                                      FStar_Pervasives_Native.Some
                                                        uu___9) in
                                                 op_let_Question uu___7
                                                   (fun sig_eff_params_bs ->
                                                      let uu___8 =
                                                        if
                                                          (FStarC_Compiler_List.length
                                                             rest_bs)
                                                            <
                                                            num_effect_params
                                                        then
                                                          FStar_Pervasives_Native.None
                                                        else
                                                          (let uu___10 =
                                                             FStarC_Compiler_List.splitAt
                                                               num_effect_params
                                                               rest_bs in
                                                           FStar_Pervasives_Native.Some
                                                             uu___10) in
                                                      op_let_Question uu___8
                                                        (fun uu___9 ->
                                                           match uu___9 with
                                                           | (eff_params_bs,
                                                              rest_bs1) ->
                                                               let uu___10 =
                                                                 eq_binders
                                                                   env
                                                                   sig_eff_params_bs
                                                                   eff_params_bs in
                                                               op_let_Question
                                                                 uu___10
                                                                 (fun
                                                                    eff_params_bs_kinds
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (eff_params_bs,
                                                                    eff_params_bs_kinds,
                                                                    rest_bs1))))) in
                                        op_let_Question uu___3
                                          (fun uu___4 ->
                                             match uu___4 with
                                             | (eff_params_bs,
                                                eff_params_bs_kinds,
                                                rest_bs1) ->
                                                 let uu___5 =
                                                   let f_sig_bs =
                                                     let uu___6 =
                                                       FStarC_TypeChecker_Env.inst_tscheme_with
                                                         m_sig_ts
                                                         [FStarC_Syntax_Syntax.U_name
                                                            u_a] in
                                                     match uu___6 with
                                                     | (uu___7, sig1) ->
                                                         let uu___8 =
                                                           let uu___9 =
                                                             FStarC_Syntax_Util.arrow_formals
                                                               sig1 in
                                                           FStar_Pervasives_Native.fst
                                                             uu___9 in
                                                         (match uu___8 with
                                                          | a::bs ->
                                                              let uu___9 =
                                                                FStarC_Compiler_List.splitAt
                                                                  num_effect_params
                                                                  bs in
                                                              (match uu___9
                                                               with
                                                               | (sig_bs,
                                                                  bs1) ->
                                                                   let ss =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    ((a.FStarC_Syntax_Syntax.binder_bv),
                                                                    uu___13) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___12 in
                                                                    [uu___11] in
                                                                    FStarC_Compiler_List.fold_left2
                                                                    (fun ss1
                                                                    ->
                                                                    fun sig_b
                                                                    ->
                                                                    fun b ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b.FStarC_Syntax_Syntax.binder_bv in
                                                                    ((sig_b.FStarC_Syntax_Syntax.binder_bv),
                                                                    uu___14) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___13 in
                                                                    [uu___12] in
                                                                    FStarC_Compiler_List.op_At
                                                                    ss1
                                                                    uu___11)
                                                                    uu___10
                                                                    sig_bs
                                                                    eff_params_bs in
                                                                   FStarC_Syntax_Subst.subst_binders
                                                                    ss bs1)) in
                                                   let uu___6 =
                                                     if
                                                       (FStarC_Compiler_List.length
                                                          rest_bs1)
                                                         <
                                                         (FStarC_Compiler_List.length
                                                            f_sig_bs)
                                                     then
                                                       FStar_Pervasives_Native.None
                                                     else
                                                       (let uu___8 =
                                                          FStarC_Compiler_List.splitAt
                                                            (FStarC_Compiler_List.length
                                                               f_sig_bs)
                                                            rest_bs1 in
                                                        FStar_Pervasives_Native.Some
                                                          uu___8) in
                                                   op_let_Question uu___6
                                                     (fun uu___7 ->
                                                        match uu___7 with
                                                        | (f_bs, rest_bs2) ->
                                                            let uu___8 =
                                                              eq_binders env
                                                                f_sig_bs f_bs in
                                                            op_let_Question
                                                              uu___8
                                                              (fun f_bs_kinds
                                                                 ->
                                                                 FStar_Pervasives_Native.Some
                                                                   (f_bs,
                                                                    f_bs_kinds,
                                                                    rest_bs2))) in
                                                 op_let_Question uu___5
                                                   (fun uu___6 ->
                                                      match uu___6 with
                                                      | (f_bs, f_bs_kinds,
                                                         rest_bs2) ->
                                                          let uu___7 =
                                                            let g_sig_bs =
                                                              let uu___8 =
                                                                FStarC_TypeChecker_Env.inst_tscheme_with
                                                                  n_sig_ts
                                                                  [FStarC_Syntax_Syntax.U_name
                                                                    u_b] in
                                                              match uu___8
                                                              with
                                                              | (uu___9,
                                                                 sig1) ->
                                                                  let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Syntax_Util.arrow_formals
                                                                    sig1 in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___11 in
                                                                  (match uu___10
                                                                   with
                                                                   | 
                                                                   b::bs ->
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Compiler_List.splitAt
                                                                    num_effect_params
                                                                    bs in
                                                                    (match uu___11
                                                                    with
                                                                    | 
                                                                    (sig_bs,
                                                                    bs1) ->
                                                                    let ss =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    ((b.FStarC_Syntax_Syntax.binder_bv),
                                                                    uu___15) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___14 in
                                                                    [uu___13] in
                                                                    FStarC_Compiler_List.fold_left2
                                                                    (fun ss1
                                                                    ->
                                                                    fun sig_b
                                                                    ->
                                                                    fun b1 ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b1.FStarC_Syntax_Syntax.binder_bv in
                                                                    ((sig_b.FStarC_Syntax_Syntax.binder_bv),
                                                                    uu___16) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___15 in
                                                                    [uu___14] in
                                                                    FStarC_Compiler_List.op_At
                                                                    ss1
                                                                    uu___13)
                                                                    uu___12
                                                                    sig_bs
                                                                    eff_params_bs in
                                                                    FStarC_Syntax_Subst.subst_binders
                                                                    ss bs1)) in
                                                            let uu___8 =
                                                              if
                                                                (FStarC_Compiler_List.length
                                                                   rest_bs2)
                                                                  <
                                                                  (FStarC_Compiler_List.length
                                                                    g_sig_bs)
                                                              then
                                                                FStar_Pervasives_Native.None
                                                              else
                                                                (let uu___10
                                                                   =
                                                                   FStarC_Compiler_List.splitAt
                                                                    (FStarC_Compiler_List.length
                                                                    g_sig_bs)
                                                                    rest_bs2 in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu___10) in
                                                            op_let_Question
                                                              uu___8
                                                              (fun uu___9 ->
                                                                 match uu___9
                                                                 with
                                                                 | (g_bs,
                                                                    rest_bs3)
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Compiler_List.fold_left2
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    fun
                                                                    g_sig_b
                                                                    ->
                                                                    fun g_b
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (l, ss)
                                                                    ->
                                                                    let g_sig_b_sort
                                                                    =
                                                                    FStarC_Syntax_Subst.subst
                                                                    ss
                                                                    (g_sig_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                                    let g_sig_b_arrow_t
                                                                    =
                                                                    let x_bv
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    FStarC_Syntax_Syntax.gen_bv
                                                                    "x"
                                                                    FStar_Pervasives_Native.None
                                                                    uu___13 in
                                                                    let ss1 =
                                                                    let uu___13
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    (bv, k1)
                                                                    ->
                                                                    if
                                                                    k1 =
                                                                    FStarC_Syntax_Syntax.Substitutive_binder
                                                                    then
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    bv in
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    x_bv in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___21 in
                                                                    [uu___20] in
                                                                    FStarC_Syntax_Syntax.mk_Tm_app
                                                                    uu___18
                                                                    uu___19
                                                                    FStarC_Compiler_Range_Type.dummyRange in
                                                                    (bv,
                                                                    uu___17) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___16 in
                                                                    [uu___15]
                                                                    else [])
                                                                    l in
                                                                    FStarC_Compiler_List.flatten
                                                                    uu___13 in
                                                                    let g_sig_b_sort1
                                                                    =
                                                                    FStarC_Syntax_Subst.subst
                                                                    ss1
                                                                    g_sig_b_sort in
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_binder
                                                                    x_bv in
                                                                    [uu___14] in
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_Total
                                                                    g_sig_b_sort1 in
                                                                    FStarC_Syntax_Util.arrow
                                                                    uu___13
                                                                    uu___14 in
                                                                    let g_b_kind
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                                                    env
                                                                    g_sig_b_arrow_t
                                                                    (g_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                                    uu___14 =
                                                                    FStarC_TypeChecker_TermEqAndSimplify.Equal in
                                                                    if
                                                                    uu___13
                                                                    then
                                                                    FStarC_Syntax_Syntax.Substitutive_binder
                                                                    else
                                                                    (let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                                                    env
                                                                    g_sig_b_sort
                                                                    (g_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                                    uu___16 =
                                                                    FStarC_TypeChecker_TermEqAndSimplify.Equal in
                                                                    if
                                                                    uu___15
                                                                    then
                                                                    FStarC_Syntax_Syntax.BindCont_no_abstraction_binder
                                                                    else
                                                                    FStarC_Syntax_Syntax.Ad_hoc_binder) in
                                                                    let ss1 =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    g_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    ((g_sig_b.FStarC_Syntax_Syntax.binder_bv),
                                                                    uu___16) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___15 in
                                                                    [uu___14] in
                                                                    FStarC_Compiler_List.op_At
                                                                    ss
                                                                    uu___13 in
                                                                    ((FStarC_Compiler_List.op_At
                                                                    l
                                                                    [
                                                                    ((g_b.FStarC_Syntax_Syntax.binder_bv),
                                                                    g_b_kind)]),
                                                                    ss1))
                                                                    ([], [])
                                                                    g_sig_bs
                                                                    g_bs in
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (g_bs_kinds,
                                                                    uu___12)
                                                                    ->
                                                                    let g_bs_kinds1
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    g_bs_kinds in
                                                                    if
                                                                    FStarC_Compiler_List.contains
                                                                    FStarC_Syntax_Syntax.Ad_hoc_binder
                                                                    g_bs_kinds1
                                                                    then
                                                                    FStar_Pervasives_Native.None
                                                                    else
                                                                    FStar_Pervasives_Native.Some
                                                                    g_bs_kinds1 in
                                                                    op_let_Question
                                                                    uu___10
                                                                    (fun
                                                                    g_bs_kinds
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (g_bs,
                                                                    g_bs_kinds,
                                                                    rest_bs3))) in
                                                          op_let_Question
                                                            uu___7
                                                            (fun uu___8 ->
                                                               match uu___8
                                                               with
                                                               | (g_bs,
                                                                  g_bs_kinds,
                                                                  rest_bs3)
                                                                   ->
                                                                   let uu___9
                                                                    =
                                                                    if
                                                                    has_range_binders
                                                                    then
                                                                    FStarC_Compiler_List.splitAt
                                                                    (Prims.of_int (2))
                                                                    rest_bs3
                                                                    else
                                                                    ([],
                                                                    rest_bs3) in
                                                                   (match uu___9
                                                                    with
                                                                    | 
                                                                    (range_bs,
                                                                    rest_bs4)
                                                                    ->
                                                                    let uu___10
                                                                    = uu___9 in
                                                                    let uu___11
                                                                    =
                                                                    if
                                                                    (FStarC_Compiler_List.length
                                                                    rest_bs4)
                                                                    >=
                                                                    (Prims.of_int (2))
                                                                    then
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Compiler_List.splitAt
                                                                    ((FStarC_Compiler_List.length
                                                                    rest_bs4)
                                                                    -
                                                                    (Prims.of_int (2)))
                                                                    rest_bs4 in
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (rest_bs5,
                                                                    f_b::g_b::[])
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (rest_bs5,
                                                                    f_b, g_b)
                                                                    else
                                                                    FStar_Pervasives_Native.None in
                                                                    op_let_Question
                                                                    uu___11
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (rest_bs5,
                                                                    f_b, g_b)
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    let repr_app_bs
                                                                    =
                                                                    FStarC_Compiler_List.op_At
                                                                    eff_params_bs
                                                                    f_bs in
                                                                    let expected_f_b_sort
                                                                    =
                                                                    match m_repr_ts
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    repr_ts
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    FStarC_TypeChecker_Env.inst_tscheme_with
                                                                    repr_ts
                                                                    [
                                                                    FStarC_Syntax_Syntax.U_name
                                                                    u_a] in
                                                                    (match uu___14
                                                                    with
                                                                    | 
                                                                    (uu___15,
                                                                    t) ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___18 in
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = b;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___20;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___21;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___22;_}
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___23)
                                                                    repr_app_bs in
                                                                    uu___17
                                                                    ::
                                                                    uu___18 in
                                                                    FStarC_Syntax_Syntax.mk_Tm_app
                                                                    t uu___16
                                                                    FStarC_Compiler_Range_Type.dummyRange)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Syntax_Syntax.null_binder
                                                                    FStarC_Syntax_Syntax.t_unit in
                                                                    [uu___15] in
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun b ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b.FStarC_Syntax_Syntax.binder_bv in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___19)
                                                                    repr_app_bs in
                                                                    {
                                                                    FStarC_Syntax_Syntax.comp_univs
                                                                    =
                                                                    [
                                                                    FStarC_Syntax_Syntax.U_name
                                                                    u_a];
                                                                    FStarC_Syntax_Syntax.effect_name
                                                                    =
                                                                    m_eff_name;
                                                                    FStarC_Syntax_Syntax.result_typ
                                                                    = uu___17;
                                                                    FStarC_Syntax_Syntax.effect_args
                                                                    = uu___18;
                                                                    FStarC_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    FStarC_Syntax_Syntax.mk_Comp
                                                                    uu___16 in
                                                                    FStarC_Syntax_Util.arrow
                                                                    uu___14
                                                                    uu___15 in
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                                                    env
                                                                    (f_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                                                    expected_f_b_sort in
                                                                    uu___15 =
                                                                    FStarC_TypeChecker_TermEqAndSimplify.Equal in
                                                                    if
                                                                    uu___14
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    ()
                                                                    else
                                                                    FStar_Pervasives_Native.None in
                                                                    op_let_Question
                                                                    uu___13
                                                                    (fun
                                                                    _f_b_ok_
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    let expected_g_b_sort
                                                                    =
                                                                    let x_bv
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    FStarC_Syntax_Syntax.gen_bv
                                                                    "x"
                                                                    FStar_Pervasives_Native.None
                                                                    uu___15 in
                                                                    let eff_params_args
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = b;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___16;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___17;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___18;_}
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___19)
                                                                    eff_params_bs in
                                                                    let g_bs_args
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Compiler_List.map2
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    fun kind
                                                                    ->
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = b;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___17;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___18;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___19;_}
                                                                    ->
                                                                    if
                                                                    kind =
                                                                    FStarC_Syntax_Syntax.Substitutive_binder
                                                                    then
                                                                    let uu___20
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    x_bv in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___23 in
                                                                    [uu___22] in
                                                                    FStarC_Syntax_Syntax.mk_Tm_app
                                                                    uu___20
                                                                    uu___21
                                                                    FStarC_Compiler_Range_Type.dummyRange
                                                                    else
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b) g_bs
                                                                    g_bs_kinds in
                                                                    FStarC_Compiler_List.map
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___15 in
                                                                    let repr_args
                                                                    =
                                                                    FStarC_Compiler_List.op_At
                                                                    eff_params_args
                                                                    g_bs_args in
                                                                    match n_repr_ts
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    repr_ts
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    FStarC_TypeChecker_Env.inst_tscheme_with
                                                                    repr_ts
                                                                    [
                                                                    FStarC_Syntax_Syntax.U_name
                                                                    u_b] in
                                                                    (match uu___15
                                                                    with
                                                                    | 
                                                                    (uu___16,
                                                                    repr_hd)
                                                                    ->
                                                                    let repr_app
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___19 in
                                                                    uu___18
                                                                    ::
                                                                    repr_args in
                                                                    FStarC_Syntax_Syntax.mk_Tm_app
                                                                    repr_hd
                                                                    uu___17
                                                                    FStarC_Compiler_Range_Type.dummyRange in
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_binder
                                                                    x_bv in
                                                                    [uu___18] in
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_Total
                                                                    repr_app in
                                                                    FStarC_Syntax_Util.arrow
                                                                    uu___17
                                                                    uu___18)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let thunk_t
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStarC_Syntax_Syntax.null_binder
                                                                    FStarC_Syntax_Syntax.t_unit in
                                                                    [uu___16] in
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    {
                                                                    FStarC_Syntax_Syntax.comp_univs
                                                                    =
                                                                    [
                                                                    FStarC_Syntax_Syntax.U_name
                                                                    u_b];
                                                                    FStarC_Syntax_Syntax.effect_name
                                                                    =
                                                                    n_eff_name;
                                                                    FStarC_Syntax_Syntax.result_typ
                                                                    = uu___18;
                                                                    FStarC_Syntax_Syntax.effect_args
                                                                    =
                                                                    repr_args;
                                                                    FStarC_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    FStarC_Syntax_Syntax.mk_Comp
                                                                    uu___17 in
                                                                    FStarC_Syntax_Util.arrow
                                                                    uu___15
                                                                    uu___16 in
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_binder
                                                                    x_bv in
                                                                    [uu___16] in
                                                                    let uu___16
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_Total
                                                                    thunk_t in
                                                                    FStarC_Syntax_Util.arrow
                                                                    uu___15
                                                                    uu___16 in
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                                                    env
                                                                    (g_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                                                    expected_g_b_sort in
                                                                    uu___16 =
                                                                    FStarC_TypeChecker_TermEqAndSimplify.Equal in
                                                                    if
                                                                    uu___15
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    ()
                                                                    else
                                                                    FStar_Pervasives_Native.None in
                                                                    op_let_Question
                                                                    uu___14
                                                                    (fun
                                                                    _g_b_ok
                                                                    ->
                                                                    let range_kinds
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStarC_Syntax_Syntax.Range_binder)
                                                                    range_bs in
                                                                    let rest_kinds
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStarC_Syntax_Syntax.Ad_hoc_binder)
                                                                    rest_bs5 in
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStarC_Compiler_List.op_At
                                                                    [FStarC_Syntax_Syntax.Type_binder;
                                                                    FStarC_Syntax_Syntax.Type_binder]
                                                                    (FStarC_Compiler_List.op_At
                                                                    eff_params_bs_kinds
                                                                    (FStarC_Compiler_List.op_At
                                                                    f_bs_kinds
                                                                    (FStarC_Compiler_List.op_At
                                                                    g_bs_kinds
                                                                    (FStarC_Compiler_List.op_At
                                                                    range_kinds
                                                                    (FStarC_Compiler_List.op_At
                                                                    rest_kinds
                                                                    [FStarC_Syntax_Syntax.Repr_binder;
                                                                    FStarC_Syntax_Syntax.Repr_binder])))))))))))))))
let (validate_indexed_effect_bind_shape :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Ident.lident ->
        FStarC_Ident.lident ->
          FStarC_Syntax_Syntax.tscheme ->
            FStarC_Syntax_Syntax.tscheme ->
              FStarC_Syntax_Syntax.tscheme ->
                FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option
                  ->
                  FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option
                    ->
                    FStarC_Syntax_Syntax.tscheme
                      FStar_Pervasives_Native.option ->
                      FStarC_Syntax_Syntax.univ_names ->
                        FStarC_Syntax_Syntax.typ ->
                          FStarC_Compiler_Range_Type.range ->
                            Prims.int ->
                              Prims.bool ->
                                (FStarC_Syntax_Syntax.typ *
                                  FStarC_Syntax_Syntax.indexed_effect_combinator_kind))
  =
  fun env ->
    fun m_eff_name ->
      fun n_eff_name ->
        fun p_eff_name ->
          fun m_sig_ts ->
            fun n_sig_ts ->
              fun p_sig_ts ->
                fun m_repr_ts ->
                  fun n_repr_ts ->
                    fun p_repr_ts ->
                      fun bind_us ->
                        fun bind_t ->
                          fun r ->
                            fun num_effect_params ->
                              fun has_range_binders ->
                                let bind_name =
                                  let uu___ =
                                    FStarC_Ident.string_of_lid m_eff_name in
                                  let uu___1 =
                                    FStarC_Ident.string_of_lid n_eff_name in
                                  let uu___2 =
                                    FStarC_Ident.string_of_lid p_eff_name in
                                  FStarC_Compiler_Util.format3
                                    "(%s , %s) |> %s" uu___ uu___1 uu___2 in
                                let uu___ = bind_us in
                                match uu___ with
                                | u_a::u_b::[] ->
                                    let a_b =
                                      let uu___1 =
                                        let uu___2 =
                                          FStarC_Syntax_Util.type_with_u
                                            (FStarC_Syntax_Syntax.U_name u_a) in
                                        FStarC_Syntax_Syntax.gen_bv "a"
                                          FStar_Pervasives_Native.None uu___2 in
                                      FStarC_Syntax_Syntax.mk_binder uu___1 in
                                    let b_b =
                                      let uu___1 =
                                        let uu___2 =
                                          FStarC_Syntax_Util.type_with_u
                                            (FStarC_Syntax_Syntax.U_name u_b) in
                                        FStarC_Syntax_Syntax.gen_bv "b"
                                          FStar_Pervasives_Native.None uu___2 in
                                      FStarC_Syntax_Syntax.mk_binder uu___1 in
                                    let rest_bs =
                                      let uu___1 =
                                        let uu___2 =
                                          FStarC_Syntax_Subst.compress bind_t in
                                        uu___2.FStarC_Syntax_Syntax.n in
                                      match uu___1 with
                                      | FStarC_Syntax_Syntax.Tm_arrow
                                          { FStarC_Syntax_Syntax.bs1 = bs;
                                            FStarC_Syntax_Syntax.comp =
                                              uu___2;_}
                                          when
                                          (FStarC_Compiler_List.length bs) >=
                                            (Prims.of_int (4))
                                          ->
                                          let uu___3 =
                                            FStarC_Syntax_Subst.open_binders
                                              bs in
                                          (match uu___3 with
                                           | {
                                               FStarC_Syntax_Syntax.binder_bv
                                                 = a;
                                               FStarC_Syntax_Syntax.binder_qual
                                                 = uu___4;
                                               FStarC_Syntax_Syntax.binder_positivity
                                                 = uu___5;
                                               FStarC_Syntax_Syntax.binder_attrs
                                                 = uu___6;_}::{
                                                                FStarC_Syntax_Syntax.binder_bv
                                                                  = b;
                                                                FStarC_Syntax_Syntax.binder_qual
                                                                  = uu___7;
                                                                FStarC_Syntax_Syntax.binder_positivity
                                                                  = uu___8;
                                                                FStarC_Syntax_Syntax.binder_attrs
                                                                  = uu___9;_}::bs1
                                               ->
                                               let uu___10 =
                                                 let uu___11 =
                                                   let uu___12 =
                                                     let uu___13 =
                                                       FStarC_Syntax_Syntax.bv_to_name
                                                         a_b.FStarC_Syntax_Syntax.binder_bv in
                                                     (a, uu___13) in
                                                   FStarC_Syntax_Syntax.NT
                                                     uu___12 in
                                                 let uu___12 =
                                                   let uu___13 =
                                                     let uu___14 =
                                                       let uu___15 =
                                                         FStarC_Syntax_Syntax.bv_to_name
                                                           b_b.FStarC_Syntax_Syntax.binder_bv in
                                                       (b, uu___15) in
                                                     FStarC_Syntax_Syntax.NT
                                                       uu___14 in
                                                   [uu___13] in
                                                 uu___11 :: uu___12 in
                                               let uu___11 =
                                                 let uu___12 =
                                                   FStarC_Compiler_List.splitAt
                                                     ((FStarC_Compiler_List.length
                                                         bs1)
                                                        - (Prims.of_int (2)))
                                                     bs1 in
                                                 FStar_Pervasives_Native.fst
                                                   uu___12 in
                                               FStarC_Syntax_Subst.subst_binders
                                                 uu___10 uu___11)
                                      | uu___2 ->
                                          let uu___3 =
                                            let uu___4 =
                                              FStarC_Class_Show.show
                                                FStarC_Syntax_Print.showable_term
                                                bind_t in
                                            FStarC_Compiler_Util.format2
                                              "Type of %s is not an arrow with >= 4 binders (%s)"
                                              bind_name uu___4 in
                                          FStarC_Errors.raise_error
                                            FStarC_Class_HasRange.hasRange_range
                                            r
                                            FStarC_Errors_Codes.Fatal_UnexpectedEffect
                                            ()
                                            (Obj.magic
                                               FStarC_Errors_Msg.is_error_message_string)
                                            (Obj.magic uu___3) in
                                    let uu___1 =
                                      if has_range_binders
                                      then
                                        (if
                                           (FStarC_Compiler_List.length
                                              rest_bs)
                                             >= (Prims.of_int (2))
                                         then
                                           FStarC_Compiler_List.splitAt
                                             ((FStarC_Compiler_List.length
                                                 rest_bs)
                                                - (Prims.of_int (2))) rest_bs
                                         else
                                           (let uu___3 =
                                              let uu___4 =
                                                FStarC_Class_Show.show
                                                  FStarC_Syntax_Print.showable_term
                                                  bind_t in
                                              FStarC_Compiler_Util.format2
                                                "Type of %s is not an arrow with >= 6 binders (%s)"
                                                bind_name uu___4 in
                                            FStarC_Errors.raise_error
                                              FStarC_Class_HasRange.hasRange_range
                                              r
                                              FStarC_Errors_Codes.Fatal_UnexpectedEffect
                                              ()
                                              (Obj.magic
                                                 FStarC_Errors_Msg.is_error_message_string)
                                              (Obj.magic uu___3)))
                                      else (rest_bs, []) in
                                    (match uu___1 with
                                     | (rest_bs1, range_bs) ->
                                         let uu___2 =
                                           let uu___3 =
                                             let uu___4 =
                                               FStarC_TypeChecker_Env.push_binders
                                                 env (a_b :: b_b :: rest_bs1) in
                                             let uu___5 =
                                               FStarC_Syntax_Syntax.bv_to_name
                                                 a_b.FStarC_Syntax_Syntax.binder_bv in
                                             FStarC_TypeChecker_Util.fresh_effect_repr
                                               uu___4 r m_eff_name m_sig_ts
                                               m_repr_ts
                                               (FStarC_Syntax_Syntax.U_name
                                                  u_a) uu___5 in
                                           match uu___3 with
                                           | (repr, g) ->
                                               let uu___4 =
                                                 let uu___5 =
                                                   FStarC_Syntax_Syntax.gen_bv
                                                     "f"
                                                     FStar_Pervasives_Native.None
                                                     repr in
                                                 FStarC_Syntax_Syntax.mk_binder
                                                   uu___5 in
                                               (uu___4, g) in
                                         (match uu___2 with
                                          | (f, guard_f) ->
                                              let uu___3 =
                                                let x_a =
                                                  let uu___4 =
                                                    let uu___5 =
                                                      FStarC_Syntax_Syntax.bv_to_name
                                                        a_b.FStarC_Syntax_Syntax.binder_bv in
                                                    FStarC_Syntax_Syntax.gen_bv
                                                      "x"
                                                      FStar_Pervasives_Native.None
                                                      uu___5 in
                                                  FStarC_Syntax_Syntax.mk_binder
                                                    uu___4 in
                                                let uu___4 =
                                                  let uu___5 =
                                                    FStarC_TypeChecker_Env.push_binders
                                                      env
                                                      (FStarC_Compiler_List.op_At
                                                         (a_b :: b_b ::
                                                         rest_bs1) [x_a]) in
                                                  let uu___6 =
                                                    FStarC_Syntax_Syntax.bv_to_name
                                                      b_b.FStarC_Syntax_Syntax.binder_bv in
                                                  FStarC_TypeChecker_Util.fresh_effect_repr
                                                    uu___5 r n_eff_name
                                                    n_sig_ts n_repr_ts
                                                    (FStarC_Syntax_Syntax.U_name
                                                       u_b) uu___6 in
                                                match uu___4 with
                                                | (repr, g) ->
                                                    let uu___5 =
                                                      let uu___6 =
                                                        let uu___7 =
                                                          let uu___8 =
                                                            FStarC_Syntax_Syntax.mk_Total
                                                              repr in
                                                          FStarC_Syntax_Util.arrow
                                                            [x_a] uu___8 in
                                                        FStarC_Syntax_Syntax.gen_bv
                                                          "g"
                                                          FStar_Pervasives_Native.None
                                                          uu___7 in
                                                      FStarC_Syntax_Syntax.mk_binder
                                                        uu___6 in
                                                    (uu___5, g) in
                                              (match uu___3 with
                                               | (g, guard_g) ->
                                                   let uu___4 =
                                                     let uu___5 =
                                                       FStarC_TypeChecker_Env.push_binders
                                                         env (a_b :: b_b ::
                                                         rest_bs1) in
                                                     let uu___6 =
                                                       FStarC_Syntax_Syntax.bv_to_name
                                                         b_b.FStarC_Syntax_Syntax.binder_bv in
                                                     FStarC_TypeChecker_Util.fresh_effect_repr
                                                       uu___5 r p_eff_name
                                                       p_sig_ts p_repr_ts
                                                       (FStarC_Syntax_Syntax.U_name
                                                          u_b) uu___6 in
                                                   (match uu___4 with
                                                    | (return_repr,
                                                       guard_return_repr) ->
                                                        let uu___5 =
                                                          let uu___6 =
                                                            FStarC_TypeChecker_Env.push_binders
                                                              env (a_b :: b_b
                                                              :: rest_bs1) in
                                                          let uu___7 =
                                                            FStarC_Compiler_Util.format1
                                                              "implicit for pure_wp in checking bind %s"
                                                              bind_name in
                                                          pure_wp_uvar uu___6
                                                            return_repr
                                                            uu___7 r in
                                                        (match uu___5 with
                                                         | (pure_wp_uvar1,
                                                            g_pure_wp_uvar)
                                                             ->
                                                             let k =
                                                               let uu___6 =
                                                                 let uu___7 =
                                                                   let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStarC_TypeChecker_Env.new_u_univ
                                                                    () in
                                                                    [uu___9] in
                                                                   let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    pure_wp_uvar1 in
                                                                    [uu___10] in
                                                                   {
                                                                    FStarC_Syntax_Syntax.comp_univs
                                                                    = uu___8;
                                                                    FStarC_Syntax_Syntax.effect_name
                                                                    =
                                                                    FStarC_Parser_Const.effect_PURE_lid;
                                                                    FStarC_Syntax_Syntax.result_typ
                                                                    =
                                                                    return_repr;
                                                                    FStarC_Syntax_Syntax.effect_args
                                                                    = uu___9;
                                                                    FStarC_Syntax_Syntax.flags
                                                                    = []
                                                                   } in
                                                                 FStarC_Syntax_Syntax.mk_Comp
                                                                   uu___7 in
                                                               FStarC_Syntax_Util.arrow
                                                                 (a_b :: b_b
                                                                 ::
                                                                 (FStarC_Compiler_List.op_At
                                                                    rest_bs1
                                                                    (
                                                                    FStarC_Compiler_List.op_At
                                                                    range_bs
                                                                    [f; g])))
                                                                 uu___6 in
                                                             let guard_eq =
                                                               let uu___6 =
                                                                 FStarC_TypeChecker_Rel.teq_nosmt
                                                                   env k
                                                                   bind_t in
                                                               match uu___6
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                   ->
                                                                   let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    bind_t in
                                                                    FStarC_Compiler_Util.format2
                                                                    "Unexpected type of %s (%s)\n"
                                                                    bind_name
                                                                    uu___8 in
                                                                   FStarC_Errors.raise_error
                                                                    FStarC_Class_HasRange.hasRange_range
                                                                    r
                                                                    FStarC_Errors_Codes.Fatal_UnexpectedEffect
                                                                    ()
                                                                    (Obj.magic
                                                                    FStarC_Errors_Msg.is_error_message_string)
                                                                    (Obj.magic
                                                                    uu___7)
                                                               | FStar_Pervasives_Native.Some
                                                                   g1 -> g1 in
                                                             ((let uu___7 =
                                                                 FStarC_TypeChecker_Env.conj_guards
                                                                   [guard_f;
                                                                   guard_g;
                                                                   guard_return_repr;
                                                                   g_pure_wp_uvar;
                                                                   guard_eq] in
                                                               FStarC_TypeChecker_Rel.force_trivial_guard
                                                                 env uu___7);
                                                              (let k1 =
                                                                 let uu___7 =
                                                                   FStarC_TypeChecker_Normalize.remove_uvar_solutions
                                                                    env k in
                                                                 FStarC_Syntax_Subst.compress
                                                                   uu___7 in
                                                               let lopt =
                                                                 bind_combinator_kind
                                                                   env
                                                                   m_eff_name
                                                                   n_eff_name
                                                                   p_eff_name
                                                                   m_sig_ts
                                                                   n_sig_ts
                                                                   p_sig_ts
                                                                   m_repr_ts
                                                                   n_repr_ts
                                                                   p_repr_ts
                                                                   bind_us k1
                                                                   num_effect_params
                                                                   has_range_binders in
                                                               let kind =
                                                                 match lopt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                    ->
                                                                    (log_ad_hoc_combinator_warning
                                                                    bind_name
                                                                    r;
                                                                    FStarC_Syntax_Syntax.Ad_hoc_combinator)
                                                                 | FStar_Pervasives_Native.Some
                                                                    l ->
                                                                    FStarC_Syntax_Syntax.Substitutive_combinator
                                                                    l in
                                                               (let uu___8 =
                                                                  (FStarC_Compiler_Debug.medium
                                                                    ()) ||
                                                                    (
                                                                    FStarC_Compiler_Effect.op_Bang
                                                                    dbg_LayeredEffectsTc) in
                                                                if uu___8
                                                                then
                                                                  let uu___9
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Syntax.showable_indexed_effect_combinator_kind
                                                                    kind in
                                                                  FStarC_Compiler_Util.print2
                                                                    "Bind %s has %s kind\n"
                                                                    bind_name
                                                                    uu___9
                                                                else ());
                                                               (k1, kind))))))))
let (subcomp_combinator_kind :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Ident.lident ->
        FStarC_Syntax_Syntax.tscheme ->
          FStarC_Syntax_Syntax.tscheme ->
            FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ->
              FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ->
                FStarC_Syntax_Syntax.univ_name ->
                  FStarC_Syntax_Syntax.typ ->
                    Prims.int ->
                      FStarC_Syntax_Syntax.indexed_effect_combinator_kind
                        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun m_eff_name ->
      fun n_eff_name ->
        fun m_sig_ts ->
          fun n_sig_ts ->
            fun m_repr_ts ->
              fun n_repr_ts ->
                fun u ->
                  fun k ->
                    fun num_effect_params ->
                      let uu___ = FStarC_Syntax_Util.arrow_formals_comp k in
                      match uu___ with
                      | (a_b::rest_bs, k_c) ->
                          let uu___1 =
                            if num_effect_params = Prims.int_zero
                            then
                              FStar_Pervasives_Native.Some ([], [], rest_bs)
                            else
                              (let uu___3 =
                                 FStarC_TypeChecker_Env.inst_tscheme_with
                                   m_sig_ts [FStarC_Syntax_Syntax.U_name u] in
                               match uu___3 with
                               | (uu___4, sig1) ->
                                   let uu___5 =
                                     FStarC_Syntax_Util.arrow_formals sig1 in
                                   (match uu___5 with
                                    | (uu___6::sig_bs, uu___7) ->
                                        let sig_effect_params_bs =
                                          let uu___8 =
                                            FStarC_Compiler_List.splitAt
                                              num_effect_params sig_bs in
                                          FStar_Pervasives_Native.fst uu___8 in
                                        let uu___8 =
                                          FStarC_Compiler_List.splitAt
                                            num_effect_params rest_bs in
                                        (match uu___8 with
                                         | (eff_params_bs, rest_bs1) ->
                                             let uu___9 =
                                               eq_binders env
                                                 sig_effect_params_bs
                                                 eff_params_bs in
                                             op_let_Question uu___9
                                               (fun eff_params_bs_kinds ->
                                                  FStar_Pervasives_Native.Some
                                                    (eff_params_bs,
                                                      eff_params_bs_kinds,
                                                      rest_bs1))))) in
                          op_let_Question uu___1
                            (fun uu___2 ->
                               match uu___2 with
                               | (eff_params_bs, eff_params_bs_kinds,
                                  rest_bs1) ->
                                   let uu___3 =
                                     let f_sig_bs =
                                       let uu___4 =
                                         FStarC_TypeChecker_Env.inst_tscheme_with
                                           m_sig_ts
                                           [FStarC_Syntax_Syntax.U_name u] in
                                       match uu___4 with
                                       | (uu___5, sig1) ->
                                           let uu___6 =
                                             let uu___7 =
                                               FStarC_Syntax_Util.arrow_formals
                                                 sig1 in
                                             FStar_Pervasives_Native.fst
                                               uu___7 in
                                           (match uu___6 with
                                            | a::bs ->
                                                let uu___7 =
                                                  FStarC_Compiler_List.splitAt
                                                    num_effect_params bs in
                                                (match uu___7 with
                                                 | (sig_bs, bs1) ->
                                                     let ss =
                                                       let uu___8 =
                                                         let uu___9 =
                                                           let uu___10 =
                                                             let uu___11 =
                                                               FStarC_Syntax_Syntax.bv_to_name
                                                                 a_b.FStarC_Syntax_Syntax.binder_bv in
                                                             ((a.FStarC_Syntax_Syntax.binder_bv),
                                                               uu___11) in
                                                           FStarC_Syntax_Syntax.NT
                                                             uu___10 in
                                                         [uu___9] in
                                                       FStarC_Compiler_List.fold_left2
                                                         (fun ss1 ->
                                                            fun sig_b ->
                                                              fun b ->
                                                                let uu___9 =
                                                                  let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b.FStarC_Syntax_Syntax.binder_bv in
                                                                    ((sig_b.FStarC_Syntax_Syntax.binder_bv),
                                                                    uu___12) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___11 in
                                                                  [uu___10] in
                                                                FStarC_Compiler_List.op_At
                                                                  ss1 uu___9)
                                                         uu___8 sig_bs
                                                         eff_params_bs in
                                                     FStarC_Syntax_Subst.subst_binders
                                                       ss bs1)) in
                                     let uu___4 =
                                       if
                                         (FStarC_Compiler_List.length
                                            rest_bs1)
                                           <
                                           (FStarC_Compiler_List.length
                                              f_sig_bs)
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu___6 =
                                            FStarC_Compiler_List.splitAt
                                              (FStarC_Compiler_List.length
                                                 f_sig_bs) rest_bs1 in
                                          FStar_Pervasives_Native.Some uu___6) in
                                     op_let_Question uu___4
                                       (fun uu___5 ->
                                          match uu___5 with
                                          | (f_bs, rest_bs2) ->
                                              let uu___6 =
                                                eq_binders env f_sig_bs f_bs in
                                              op_let_Question uu___6
                                                (fun f_bs_kinds ->
                                                   FStar_Pervasives_Native.Some
                                                     (f_bs, f_bs_kinds,
                                                       rest_bs2))) in
                                   op_let_Question uu___3
                                     (fun uu___4 ->
                                        match uu___4 with
                                        | (f_bs, f_bs_kinds, rest_bs2) ->
                                            let uu___5 =
                                              if
                                                (FStarC_Compiler_List.length
                                                   rest_bs2)
                                                  >= Prims.int_one
                                              then
                                                let uu___6 =
                                                  FStarC_Compiler_List.splitAt
                                                    ((FStarC_Compiler_List.length
                                                        rest_bs2)
                                                       - Prims.int_one)
                                                    rest_bs2 in
                                                match uu___6 with
                                                | (rest_bs3, f_b::[]) ->
                                                    FStar_Pervasives_Native.Some
                                                      (rest_bs3, f_b)
                                              else
                                                FStar_Pervasives_Native.None in
                                            op_let_Question uu___5
                                              (fun uu___6 ->
                                                 match uu___6 with
                                                 | (rest_bs3, f_b) ->
                                                     let uu___7 =
                                                       let expected_f_b_sort
                                                         =
                                                         match m_repr_ts with
                                                         | FStar_Pervasives_Native.Some
                                                             repr_ts ->
                                                             let uu___8 =
                                                               FStarC_TypeChecker_Env.inst_tscheme_with
                                                                 repr_ts
                                                                 [FStarC_Syntax_Syntax.U_name
                                                                    u] in
                                                             (match uu___8
                                                              with
                                                              | (uu___9, t)
                                                                  ->
                                                                  let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___12 in
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = b;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___14;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___15;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___16;_}
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___17)
                                                                    (FStarC_Compiler_List.op_At
                                                                    eff_params_bs
                                                                    f_bs) in
                                                                    uu___11
                                                                    ::
                                                                    uu___12 in
                                                                  FStarC_Syntax_Syntax.mk_Tm_app
                                                                    t uu___10
                                                                    FStarC_Compiler_Range_Type.dummyRange)
                                                         | FStar_Pervasives_Native.None
                                                             ->
                                                             let uu___8 =
                                                               let uu___9 =
                                                                 FStarC_Syntax_Syntax.null_binder
                                                                   FStarC_Syntax_Syntax.t_unit in
                                                               [uu___9] in
                                                             let uu___9 =
                                                               let uu___10 =
                                                                 let uu___11
                                                                   =
                                                                   FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                 let uu___12
                                                                   =
                                                                   FStarC_Compiler_List.map
                                                                    (fun b ->
                                                                    let uu___13
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b.FStarC_Syntax_Syntax.binder_bv in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___13)
                                                                    (FStarC_Compiler_List.op_At
                                                                    eff_params_bs
                                                                    f_bs) in
                                                                 {
                                                                   FStarC_Syntax_Syntax.comp_univs
                                                                    =
                                                                    [
                                                                    FStarC_Syntax_Syntax.U_name
                                                                    u];
                                                                   FStarC_Syntax_Syntax.effect_name
                                                                    =
                                                                    m_eff_name;
                                                                   FStarC_Syntax_Syntax.result_typ
                                                                    = uu___11;
                                                                   FStarC_Syntax_Syntax.effect_args
                                                                    = uu___12;
                                                                   FStarC_Syntax_Syntax.flags
                                                                    = []
                                                                 } in
                                                               FStarC_Syntax_Syntax.mk_Comp
                                                                 uu___10 in
                                                             FStarC_Syntax_Util.arrow
                                                               uu___8 uu___9 in
                                                       let uu___8 =
                                                         let uu___9 =
                                                           FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                                             env
                                                             (f_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                                             expected_f_b_sort in
                                                         uu___9 =
                                                           FStarC_TypeChecker_TermEqAndSimplify.Equal in
                                                       if uu___8
                                                       then
                                                         FStar_Pervasives_Native.Some
                                                           ()
                                                       else
                                                         FStar_Pervasives_Native.None in
                                                     op_let_Question uu___7
                                                       (fun _f_b_ok_ ->
                                                          let check_ret_t
                                                            f_or_g_bs =
                                                            let expected_t =
                                                              match n_repr_ts
                                                              with
                                                              | FStar_Pervasives_Native.Some
                                                                  repr_ts ->
                                                                  let uu___8
                                                                    =
                                                                    FStarC_TypeChecker_Env.inst_tscheme_with
                                                                    repr_ts
                                                                    [
                                                                    FStarC_Syntax_Syntax.U_name
                                                                    u] in
                                                                  (match uu___8
                                                                   with
                                                                   | 
                                                                   (uu___9,
                                                                    t) ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___12 in
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = b;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___14;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___15;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___16;_}
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___17)
                                                                    (FStarC_Compiler_List.op_At
                                                                    eff_params_bs
                                                                    f_or_g_bs) in
                                                                    uu___11
                                                                    ::
                                                                    uu___12 in
                                                                    FStarC_Syntax_Syntax.mk_Tm_app
                                                                    t uu___10
                                                                    FStarC_Compiler_Range_Type.dummyRange)
                                                              | FStar_Pervasives_Native.None
                                                                  ->
                                                                  let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Syntax_Syntax.null_binder
                                                                    FStarC_Syntax_Syntax.t_unit in
                                                                    [uu___9] in
                                                                  let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun b ->
                                                                    let uu___13
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b.FStarC_Syntax_Syntax.binder_bv in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___13)
                                                                    (FStarC_Compiler_List.op_At
                                                                    eff_params_bs
                                                                    f_or_g_bs) in
                                                                    {
                                                                    FStarC_Syntax_Syntax.comp_univs
                                                                    =
                                                                    [
                                                                    FStarC_Syntax_Syntax.U_name
                                                                    u];
                                                                    FStarC_Syntax_Syntax.effect_name
                                                                    =
                                                                    n_eff_name;
                                                                    FStarC_Syntax_Syntax.result_typ
                                                                    = uu___11;
                                                                    FStarC_Syntax_Syntax.effect_args
                                                                    = uu___12;
                                                                    FStarC_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    FStarC_Syntax_Syntax.mk_Comp
                                                                    uu___10 in
                                                                  FStarC_Syntax_Util.arrow
                                                                    uu___8
                                                                    uu___9 in
                                                            let uu___8 =
                                                              let uu___9 =
                                                                FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                                                  env
                                                                  (FStarC_Syntax_Util.comp_result
                                                                    k_c)
                                                                  expected_t in
                                                              uu___9 =
                                                                FStarC_TypeChecker_TermEqAndSimplify.Equal in
                                                            if uu___8
                                                            then
                                                              FStar_Pervasives_Native.Some
                                                                ()
                                                            else
                                                              FStar_Pervasives_Native.None in
                                                          let uu___8 =
                                                            let uu___9 =
                                                              check_ret_t
                                                                f_bs in
                                                            FStar_Pervasives_Native.uu___is_Some
                                                              uu___9 in
                                                          if uu___8
                                                          then
                                                            FStar_Pervasives_Native.Some
                                                              FStarC_Syntax_Syntax.Substitutive_invariant_combinator
                                                          else
                                                            (let uu___10 =
                                                               let g_sig_bs =
                                                                 let uu___11
                                                                   =
                                                                   FStarC_TypeChecker_Env.inst_tscheme_with
                                                                    n_sig_ts
                                                                    [
                                                                    FStarC_Syntax_Syntax.U_name
                                                                    u] in
                                                                 match uu___11
                                                                 with
                                                                 | (uu___12,
                                                                    sig1) ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Syntax_Util.arrow_formals
                                                                    sig1 in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___14 in
                                                                    (match uu___13
                                                                    with
                                                                    | 
                                                                    a::bs ->
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Compiler_List.splitAt
                                                                    num_effect_params
                                                                    bs in
                                                                    (match uu___14
                                                                    with
                                                                    | 
                                                                    (sig_bs,
                                                                    bs1) ->
                                                                    let ss =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    ((a.FStarC_Syntax_Syntax.binder_bv),
                                                                    uu___18) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___17 in
                                                                    [uu___16] in
                                                                    FStarC_Compiler_List.fold_left2
                                                                    (fun ss1
                                                                    ->
                                                                    fun sig_b
                                                                    ->
                                                                    fun b ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b.FStarC_Syntax_Syntax.binder_bv in
                                                                    ((sig_b.FStarC_Syntax_Syntax.binder_bv),
                                                                    uu___19) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___18 in
                                                                    [uu___17] in
                                                                    FStarC_Compiler_List.op_At
                                                                    ss1
                                                                    uu___16)
                                                                    uu___15
                                                                    sig_bs
                                                                    eff_params_bs in
                                                                    FStarC_Syntax_Subst.subst_binders
                                                                    ss bs1)) in
                                                               let uu___11 =
                                                                 if
                                                                   (FStarC_Compiler_List.length
                                                                    rest_bs3)
                                                                    <
                                                                    (FStarC_Compiler_List.length
                                                                    g_sig_bs)
                                                                 then
                                                                   FStar_Pervasives_Native.None
                                                                 else
                                                                   (let uu___13
                                                                    =
                                                                    FStarC_Compiler_List.splitAt
                                                                    (FStarC_Compiler_List.length
                                                                    g_sig_bs)
                                                                    rest_bs3 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___13) in
                                                               op_let_Question
                                                                 uu___11
                                                                 (fun uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (g_bs,
                                                                    rest_bs4)
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    eq_binders
                                                                    env
                                                                    g_sig_bs
                                                                    g_bs in
                                                                    op_let_Question
                                                                    uu___13
                                                                    (fun
                                                                    g_bs_kinds
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (g_bs,
                                                                    g_bs_kinds,
                                                                    rest_bs4))) in
                                                             op_let_Question
                                                               uu___10
                                                               (fun uu___11
                                                                  ->
                                                                  match uu___11
                                                                  with
                                                                  | (g_bs,
                                                                    g_bs_kinds,
                                                                    rest_bs4)
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    check_ret_t
                                                                    g_bs in
                                                                    op_let_Question
                                                                    uu___12
                                                                    (fun
                                                                    _ret_t_ok_
                                                                    ->
                                                                    let rest_kinds
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStarC_Syntax_Syntax.Ad_hoc_binder)
                                                                    rest_bs4 in
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStarC_Syntax_Syntax.Substitutive_combinator
                                                                    (FStarC_Compiler_List.op_At
                                                                    [FStarC_Syntax_Syntax.Type_binder]
                                                                    (FStarC_Compiler_List.op_At
                                                                    eff_params_bs_kinds
                                                                    (FStarC_Compiler_List.op_At
                                                                    f_bs_kinds
                                                                    (FStarC_Compiler_List.op_At
                                                                    g_bs_kinds
                                                                    (FStarC_Compiler_List.op_At
                                                                    rest_kinds
                                                                    [FStarC_Syntax_Syntax.Repr_binder])))))))))))))
let (validate_indexed_effect_subcomp_shape :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Ident.lident ->
        FStarC_Syntax_Syntax.tscheme ->
          FStarC_Syntax_Syntax.tscheme ->
            FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ->
              FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ->
                FStarC_Syntax_Syntax.univ_name ->
                  FStarC_Syntax_Syntax.typ ->
                    Prims.int ->
                      FStarC_Compiler_Range_Type.range ->
                        (FStarC_Syntax_Syntax.typ *
                          FStarC_Syntax_Syntax.indexed_effect_combinator_kind))
  =
  fun env ->
    fun m_eff_name ->
      fun n_eff_name ->
        fun m_sig_ts ->
          fun n_sig_ts ->
            fun m_repr_ts ->
              fun n_repr_ts ->
                fun u ->
                  fun subcomp_t ->
                    fun num_effect_params ->
                      fun r ->
                        let subcomp_name =
                          let uu___ = FStarC_Ident.string_of_lid m_eff_name in
                          let uu___1 = FStarC_Ident.string_of_lid n_eff_name in
                          FStarC_Compiler_Util.format2 "%s <: %s" uu___
                            uu___1 in
                        let a_b =
                          let uu___ =
                            let uu___1 =
                              FStarC_Syntax_Util.type_with_u
                                (FStarC_Syntax_Syntax.U_name u) in
                            FStarC_Syntax_Syntax.gen_bv "a"
                              FStar_Pervasives_Native.None uu___1 in
                          FStarC_Syntax_Syntax.mk_binder uu___ in
                        let rest_bs =
                          let uu___ =
                            let uu___1 =
                              FStarC_Syntax_Subst.compress subcomp_t in
                            uu___1.FStarC_Syntax_Syntax.n in
                          match uu___ with
                          | FStarC_Syntax_Syntax.Tm_arrow
                              { FStarC_Syntax_Syntax.bs1 = bs;
                                FStarC_Syntax_Syntax.comp = uu___1;_}
                              when
                              (FStarC_Compiler_List.length bs) >=
                                (Prims.of_int (2))
                              ->
                              let uu___2 =
                                FStarC_Syntax_Subst.open_binders bs in
                              (match uu___2 with
                               | { FStarC_Syntax_Syntax.binder_bv = a;
                                   FStarC_Syntax_Syntax.binder_qual = uu___3;
                                   FStarC_Syntax_Syntax.binder_positivity =
                                     uu___4;
                                   FStarC_Syntax_Syntax.binder_attrs = uu___5;_}::bs1
                                   ->
                                   let uu___6 =
                                     let uu___7 =
                                       let uu___8 =
                                         let uu___9 =
                                           FStarC_Syntax_Syntax.bv_to_name
                                             a_b.FStarC_Syntax_Syntax.binder_bv in
                                         (a, uu___9) in
                                       FStarC_Syntax_Syntax.NT uu___8 in
                                     [uu___7] in
                                   let uu___7 =
                                     let uu___8 =
                                       FStarC_Compiler_List.splitAt
                                         ((FStarC_Compiler_List.length bs1) -
                                            Prims.int_one) bs1 in
                                     FStar_Pervasives_Native.fst uu___8 in
                                   FStarC_Syntax_Subst.subst_binders uu___6
                                     uu___7)
                          | uu___1 ->
                              let uu___2 =
                                let uu___3 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term
                                    subcomp_t in
                                FStarC_Compiler_Util.format2
                                  "Type of %s is not an arrow with >= 2 binders (%s)"
                                  subcomp_name uu___3 in
                              FStarC_Errors.raise_error
                                FStarC_Class_HasRange.hasRange_range r
                                FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                                (Obj.magic
                                   FStarC_Errors_Msg.is_error_message_string)
                                (Obj.magic uu___2) in
                        let uu___ =
                          let uu___1 =
                            let uu___2 =
                              FStarC_TypeChecker_Env.push_binders env (a_b ::
                                rest_bs) in
                            let uu___3 =
                              FStarC_Syntax_Syntax.bv_to_name
                                a_b.FStarC_Syntax_Syntax.binder_bv in
                            FStarC_TypeChecker_Util.fresh_effect_repr uu___2
                              r m_eff_name m_sig_ts m_repr_ts
                              (FStarC_Syntax_Syntax.U_name u) uu___3 in
                          match uu___1 with
                          | (repr, g) ->
                              let uu___2 =
                                let uu___3 =
                                  FStarC_Syntax_Syntax.gen_bv "f"
                                    FStar_Pervasives_Native.None repr in
                                FStarC_Syntax_Syntax.mk_binder uu___3 in
                              (uu___2, g) in
                        match uu___ with
                        | (f, guard_f) ->
                            let uu___1 =
                              let uu___2 =
                                FStarC_TypeChecker_Env.push_binders env (a_b
                                  :: rest_bs) in
                              let uu___3 =
                                FStarC_Syntax_Syntax.bv_to_name
                                  a_b.FStarC_Syntax_Syntax.binder_bv in
                              FStarC_TypeChecker_Util.fresh_effect_repr
                                uu___2 r n_eff_name n_sig_ts n_repr_ts
                                (FStarC_Syntax_Syntax.U_name u) uu___3 in
                            (match uu___1 with
                             | (ret_t, guard_ret_t) ->
                                 let uu___2 =
                                   let uu___3 =
                                     FStarC_TypeChecker_Env.push_binders env
                                       (a_b :: rest_bs) in
                                   let uu___4 =
                                     FStarC_Compiler_Util.format1
                                       "implicit for pure_wp in checking %s"
                                       subcomp_name in
                                   pure_wp_uvar uu___3 ret_t uu___4 r in
                                 (match uu___2 with
                                  | (pure_wp_uvar1, guard_wp) ->
                                      let c =
                                        let uu___3 =
                                          let uu___4 =
                                            let uu___5 =
                                              FStarC_TypeChecker_Env.new_u_univ
                                                () in
                                            [uu___5] in
                                          let uu___5 =
                                            let uu___6 =
                                              FStarC_Syntax_Syntax.as_arg
                                                pure_wp_uvar1 in
                                            [uu___6] in
                                          {
                                            FStarC_Syntax_Syntax.comp_univs =
                                              uu___4;
                                            FStarC_Syntax_Syntax.effect_name
                                              =
                                              FStarC_Parser_Const.effect_PURE_lid;
                                            FStarC_Syntax_Syntax.result_typ =
                                              ret_t;
                                            FStarC_Syntax_Syntax.effect_args
                                              = uu___5;
                                            FStarC_Syntax_Syntax.flags = []
                                          } in
                                        FStarC_Syntax_Syntax.mk_Comp uu___3 in
                                      let k =
                                        FStarC_Syntax_Util.arrow
                                          (FStarC_Compiler_List.op_At (a_b ::
                                             rest_bs) [f]) c in
                                      ((let uu___4 =
                                          (FStarC_Compiler_Debug.medium ())
                                            ||
                                            (FStarC_Compiler_Effect.op_Bang
                                               dbg_LayeredEffectsTc) in
                                        if uu___4
                                        then
                                          let uu___5 =
                                            FStarC_Class_Show.show
                                              FStarC_Syntax_Print.showable_term
                                              k in
                                          FStarC_Compiler_Util.print1
                                            "Expected type of subcomp before unification: %s\n"
                                            uu___5
                                        else ());
                                       (let guard_eq =
                                          let uu___4 =
                                            FStarC_TypeChecker_Rel.teq_nosmt
                                              env subcomp_t k in
                                          match uu___4 with
                                          | FStar_Pervasives_Native.None ->
                                              let uu___5 =
                                                let uu___6 =
                                                  FStarC_Class_Show.show
                                                    FStarC_Syntax_Print.showable_term
                                                    subcomp_t in
                                                FStarC_Compiler_Util.format2
                                                  "Unexpected type of %s (%s)\n"
                                                  subcomp_name uu___6 in
                                              FStarC_Errors.raise_error
                                                FStarC_Class_HasRange.hasRange_range
                                                r
                                                FStarC_Errors_Codes.Fatal_UnexpectedEffect
                                                ()
                                                (Obj.magic
                                                   FStarC_Errors_Msg.is_error_message_string)
                                                (Obj.magic uu___5)
                                          | FStar_Pervasives_Native.Some g ->
                                              g in
                                        (let uu___5 =
                                           FStarC_TypeChecker_Env.conj_guards
                                             [guard_f;
                                             guard_ret_t;
                                             guard_wp;
                                             guard_eq] in
                                         FStarC_TypeChecker_Rel.force_trivial_guard
                                           env uu___5);
                                        (let k1 =
                                           let uu___5 =
                                             FStarC_TypeChecker_Normalize.remove_uvar_solutions
                                               env k in
                                           FStarC_Syntax_Subst.compress
                                             uu___5 in
                                         let kopt =
                                           subcomp_combinator_kind env
                                             m_eff_name n_eff_name m_sig_ts
                                             n_sig_ts m_repr_ts n_repr_ts u
                                             k1 num_effect_params in
                                         let kind =
                                           match kopt with
                                           | FStar_Pervasives_Native.None ->
                                               (log_ad_hoc_combinator_warning
                                                  subcomp_name r;
                                                FStarC_Syntax_Syntax.Ad_hoc_combinator)
                                           | FStar_Pervasives_Native.Some k2
                                               -> k2 in
                                         (let uu___6 =
                                            (FStarC_Compiler_Debug.medium ())
                                              ||
                                              (FStarC_Compiler_Effect.op_Bang
                                                 dbg_LayeredEffectsTc) in
                                          if uu___6
                                          then
                                            let uu___7 =
                                              FStarC_Class_Show.show
                                                FStarC_Syntax_Syntax.showable_indexed_effect_combinator_kind
                                                kind in
                                            FStarC_Compiler_Util.print2
                                              "Subcomp %s has %s kind\n"
                                              subcomp_name uu___7
                                          else ());
                                         (k1, kind))))))
let (ite_combinator_kind :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Syntax_Syntax.tscheme ->
        FStarC_Syntax_Syntax.tscheme ->
          FStarC_Syntax_Syntax.univ_name ->
            FStarC_Syntax_Syntax.term ->
              Prims.int ->
                FStarC_Syntax_Syntax.indexed_effect_combinator_kind
                  FStar_Pervasives_Native.option)
  =
  fun env ->
    fun eff_name ->
      fun sig_ts ->
        fun repr_ts ->
          fun u ->
            fun tm ->
              fun num_effect_params ->
                let uu___ = FStarC_Syntax_Util.abs_formals tm in
                match uu___ with
                | (a_b::rest_bs, uu___1, uu___2) ->
                    let uu___3 =
                      if num_effect_params = Prims.int_zero
                      then FStar_Pervasives_Native.Some ([], [], rest_bs)
                      else
                        (let uu___5 =
                           FStarC_TypeChecker_Env.inst_tscheme_with sig_ts
                             [FStarC_Syntax_Syntax.U_name u] in
                         match uu___5 with
                         | (uu___6, sig1) ->
                             let uu___7 =
                               FStarC_Syntax_Util.arrow_formals sig1 in
                             (match uu___7 with
                              | (uu___8::sig_bs, uu___9) ->
                                  let sig_effect_params_bs =
                                    let uu___10 =
                                      FStarC_Compiler_List.splitAt
                                        num_effect_params sig_bs in
                                    FStar_Pervasives_Native.fst uu___10 in
                                  let uu___10 =
                                    FStarC_Compiler_List.splitAt
                                      num_effect_params rest_bs in
                                  (match uu___10 with
                                   | (eff_params_bs, rest_bs1) ->
                                       let uu___11 =
                                         eq_binders env sig_effect_params_bs
                                           eff_params_bs in
                                       op_let_Question uu___11
                                         (fun eff_params_bs_kinds ->
                                            FStar_Pervasives_Native.Some
                                              (eff_params_bs,
                                                eff_params_bs_kinds,
                                                rest_bs1))))) in
                    op_let_Question uu___3
                      (fun uu___4 ->
                         match uu___4 with
                         | (eff_params_bs, eff_params_bs_kinds, rest_bs1) ->
                             let uu___5 =
                               let f_sig_bs =
                                 let uu___6 =
                                   FStarC_TypeChecker_Env.inst_tscheme_with
                                     sig_ts [FStarC_Syntax_Syntax.U_name u] in
                                 match uu___6 with
                                 | (uu___7, sig1) ->
                                     let uu___8 =
                                       let uu___9 =
                                         FStarC_Syntax_Util.arrow_formals
                                           sig1 in
                                       FStar_Pervasives_Native.fst uu___9 in
                                     (match uu___8 with
                                      | a::bs ->
                                          let uu___9 =
                                            FStarC_Compiler_List.splitAt
                                              num_effect_params bs in
                                          (match uu___9 with
                                           | (sig_bs, bs1) ->
                                               let ss =
                                                 let uu___10 =
                                                   let uu___11 =
                                                     let uu___12 =
                                                       let uu___13 =
                                                         FStarC_Syntax_Syntax.bv_to_name
                                                           a_b.FStarC_Syntax_Syntax.binder_bv in
                                                       ((a.FStarC_Syntax_Syntax.binder_bv),
                                                         uu___13) in
                                                     FStarC_Syntax_Syntax.NT
                                                       uu___12 in
                                                   [uu___11] in
                                                 FStarC_Compiler_List.fold_left2
                                                   (fun ss1 ->
                                                      fun sig_b ->
                                                        fun b ->
                                                          let uu___11 =
                                                            let uu___12 =
                                                              let uu___13 =
                                                                let uu___14 =
                                                                  FStarC_Syntax_Syntax.bv_to_name
                                                                    b.FStarC_Syntax_Syntax.binder_bv in
                                                                ((sig_b.FStarC_Syntax_Syntax.binder_bv),
                                                                  uu___14) in
                                                              FStarC_Syntax_Syntax.NT
                                                                uu___13 in
                                                            [uu___12] in
                                                          FStarC_Compiler_List.op_At
                                                            ss1 uu___11)
                                                   uu___10 sig_bs
                                                   eff_params_bs in
                                               FStarC_Syntax_Subst.subst_binders
                                                 ss bs1)) in
                               let uu___6 =
                                 if
                                   (FStarC_Compiler_List.length rest_bs1) <
                                     (FStarC_Compiler_List.length f_sig_bs)
                                 then FStar_Pervasives_Native.None
                                 else
                                   (let uu___8 =
                                      FStarC_Compiler_List.splitAt
                                        (FStarC_Compiler_List.length f_sig_bs)
                                        rest_bs1 in
                                    FStar_Pervasives_Native.Some uu___8) in
                               op_let_Question uu___6
                                 (fun uu___7 ->
                                    match uu___7 with
                                    | (f_bs, rest_bs2) ->
                                        let uu___8 =
                                          eq_binders env f_sig_bs f_bs in
                                        op_let_Question uu___8
                                          (fun f_bs_kinds ->
                                             FStar_Pervasives_Native.Some
                                               (f_bs, f_bs_kinds, rest_bs2))) in
                             op_let_Question uu___5
                               (fun uu___6 ->
                                  match uu___6 with
                                  | (f_bs, f_bs_kinds, rest_bs2) ->
                                      let uu___7 =
                                        if
                                          (FStarC_Compiler_List.length
                                             rest_bs2)
                                            >= (Prims.of_int (3))
                                        then
                                          let uu___8 =
                                            FStarC_Compiler_List.splitAt
                                              ((FStarC_Compiler_List.length
                                                  rest_bs2)
                                                 - (Prims.of_int (3)))
                                              rest_bs2 in
                                          FStar_Pervasives_Native.Some uu___8
                                        else FStar_Pervasives_Native.None in
                                      op_let_Question uu___7
                                        (fun uu___8 ->
                                           match uu___8 with
                                           | (rest_bs3, f_b::g_b::p_b::[]) ->
                                               let uu___9 =
                                                 let expected_f_b_sort =
                                                   let uu___10 =
                                                     FStarC_TypeChecker_Env.inst_tscheme_with
                                                       repr_ts
                                                       [FStarC_Syntax_Syntax.U_name
                                                          u] in
                                                   match uu___10 with
                                                   | (uu___11, t) ->
                                                       let uu___12 =
                                                         let uu___13 =
                                                           let uu___14 =
                                                             FStarC_Syntax_Syntax.bv_to_name
                                                               a_b.FStarC_Syntax_Syntax.binder_bv in
                                                           FStarC_Syntax_Syntax.as_arg
                                                             uu___14 in
                                                         let uu___14 =
                                                           FStarC_Compiler_List.map
                                                             (fun uu___15 ->
                                                                match uu___15
                                                                with
                                                                | {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = b;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___16;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___17;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___18;_}
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___19)
                                                             (FStarC_Compiler_List.op_At
                                                                eff_params_bs
                                                                f_bs) in
                                                         uu___13 :: uu___14 in
                                                       FStarC_Syntax_Syntax.mk_Tm_app
                                                         t uu___12
                                                         FStarC_Compiler_Range_Type.dummyRange in
                                                 let uu___10 =
                                                   let uu___11 =
                                                     FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                                       env
                                                       (f_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                                       expected_f_b_sort in
                                                   uu___11 =
                                                     FStarC_TypeChecker_TermEqAndSimplify.Equal in
                                                 if uu___10
                                                 then
                                                   FStar_Pervasives_Native.Some
                                                     ()
                                                 else
                                                   FStar_Pervasives_Native.None in
                                               op_let_Question uu___9
                                                 (fun _f_b_ok_ ->
                                                    let check_g_b f_or_g_bs =
                                                      let expected_g_b_sort =
                                                        let uu___10 =
                                                          FStarC_TypeChecker_Env.inst_tscheme_with
                                                            repr_ts
                                                            [FStarC_Syntax_Syntax.U_name
                                                               u] in
                                                        match uu___10 with
                                                        | (uu___11, t) ->
                                                            let uu___12 =
                                                              let uu___13 =
                                                                let uu___14 =
                                                                  FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                FStarC_Syntax_Syntax.as_arg
                                                                  uu___14 in
                                                              let uu___14 =
                                                                FStarC_Compiler_List.map
                                                                  (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = b;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___16;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___17;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___18;_}
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___19)
                                                                  (FStarC_Compiler_List.op_At
                                                                    eff_params_bs
                                                                    f_or_g_bs) in
                                                              uu___13 ::
                                                                uu___14 in
                                                            FStarC_Syntax_Syntax.mk_Tm_app
                                                              t uu___12
                                                              FStarC_Compiler_Range_Type.dummyRange in
                                                      let uu___10 =
                                                        let uu___11 =
                                                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                                            env
                                                            (g_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                                            expected_g_b_sort in
                                                        uu___11 =
                                                          FStarC_TypeChecker_TermEqAndSimplify.Equal in
                                                      if uu___10
                                                      then
                                                        FStar_Pervasives_Native.Some
                                                          ()
                                                      else
                                                        FStar_Pervasives_Native.None in
                                                    let uu___10 =
                                                      let uu___11 =
                                                        check_g_b f_bs in
                                                      FStar_Pervasives_Native.uu___is_Some
                                                        uu___11 in
                                                    if uu___10
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        FStarC_Syntax_Syntax.Substitutive_invariant_combinator
                                                    else
                                                      (let uu___12 =
                                                         let g_sig_bs =
                                                           let uu___13 =
                                                             FStarC_TypeChecker_Env.inst_tscheme_with
                                                               sig_ts
                                                               [FStarC_Syntax_Syntax.U_name
                                                                  u] in
                                                           match uu___13 with
                                                           | (uu___14, sig1)
                                                               ->
                                                               let uu___15 =
                                                                 let uu___16
                                                                   =
                                                                   FStarC_Syntax_Util.arrow_formals
                                                                    sig1 in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu___16 in
                                                               (match uu___15
                                                                with
                                                                | a::bs ->
                                                                    let uu___16
                                                                    =
                                                                    FStarC_Compiler_List.splitAt
                                                                    num_effect_params
                                                                    bs in
                                                                    (match uu___16
                                                                    with
                                                                    | 
                                                                    (sig_bs,
                                                                    bs1) ->
                                                                    let ss =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    ((a.FStarC_Syntax_Syntax.binder_bv),
                                                                    uu___20) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___19 in
                                                                    [uu___18] in
                                                                    FStarC_Compiler_List.fold_left2
                                                                    (fun ss1
                                                                    ->
                                                                    fun sig_b
                                                                    ->
                                                                    fun b ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b.FStarC_Syntax_Syntax.binder_bv in
                                                                    ((sig_b.FStarC_Syntax_Syntax.binder_bv),
                                                                    uu___21) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___20 in
                                                                    [uu___19] in
                                                                    FStarC_Compiler_List.op_At
                                                                    ss1
                                                                    uu___18)
                                                                    uu___17
                                                                    sig_bs
                                                                    eff_params_bs in
                                                                    FStarC_Syntax_Subst.subst_binders
                                                                    ss bs1)) in
                                                         let uu___13 =
                                                           if
                                                             (FStarC_Compiler_List.length
                                                                rest_bs3)
                                                               <
                                                               (FStarC_Compiler_List.length
                                                                  g_sig_bs)
                                                           then
                                                             FStar_Pervasives_Native.None
                                                           else
                                                             (let uu___15 =
                                                                FStarC_Compiler_List.splitAt
                                                                  (FStarC_Compiler_List.length
                                                                    g_sig_bs)
                                                                  rest_bs3 in
                                                              FStar_Pervasives_Native.Some
                                                                uu___15) in
                                                         op_let_Question
                                                           uu___13
                                                           (fun uu___14 ->
                                                              match uu___14
                                                              with
                                                              | (g_bs,
                                                                 rest_bs4) ->
                                                                  let uu___15
                                                                    =
                                                                    eq_binders
                                                                    env
                                                                    g_sig_bs
                                                                    g_bs in
                                                                  op_let_Question
                                                                    uu___15
                                                                    (
                                                                    fun
                                                                    g_bs_kinds
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (g_bs,
                                                                    g_bs_kinds,
                                                                    rest_bs4))) in
                                                       op_let_Question
                                                         uu___12
                                                         (fun uu___13 ->
                                                            match uu___13
                                                            with
                                                            | (g_bs,
                                                               g_bs_kinds,
                                                               rest_bs4) ->
                                                                let uu___14 =
                                                                  check_g_b
                                                                    g_bs in
                                                                op_let_Question
                                                                  uu___14
                                                                  (fun
                                                                    _g_b_ok_
                                                                    ->
                                                                    let rest_kinds
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStarC_Syntax_Syntax.Ad_hoc_binder)
                                                                    rest_bs4 in
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStarC_Syntax_Syntax.Substitutive_combinator
                                                                    (FStarC_Compiler_List.op_At
                                                                    [FStarC_Syntax_Syntax.Type_binder]
                                                                    (FStarC_Compiler_List.op_At
                                                                    eff_params_bs_kinds
                                                                    (FStarC_Compiler_List.op_At
                                                                    f_bs_kinds
                                                                    (FStarC_Compiler_List.op_At
                                                                    g_bs_kinds
                                                                    (FStarC_Compiler_List.op_At
                                                                    rest_kinds
                                                                    [FStarC_Syntax_Syntax.Repr_binder;
                                                                    FStarC_Syntax_Syntax.Repr_binder;
                                                                    FStarC_Syntax_Syntax.Substitutive_binder])))))))))))))
let (validate_indexed_effect_ite_shape :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Syntax_Syntax.tscheme ->
        FStarC_Syntax_Syntax.tscheme ->
          FStarC_Syntax_Syntax.univ_name ->
            FStarC_Syntax_Syntax.typ ->
              FStarC_Syntax_Syntax.term ->
                Prims.int ->
                  FStarC_Compiler_Range_Type.range ->
                    (FStarC_Syntax_Syntax.term *
                      FStarC_Syntax_Syntax.indexed_effect_combinator_kind))
  =
  fun env ->
    fun eff_name ->
      fun sig_ts ->
        fun repr_ts ->
          fun u ->
            fun ite_ty ->
              fun ite_tm ->
                fun num_effect_params ->
                  fun r ->
                    let ite_name =
                      let uu___ = FStarC_Ident.string_of_lid eff_name in
                      FStarC_Compiler_Util.format1 "ite_%s" uu___ in
                    let a_b =
                      let uu___ =
                        let uu___1 =
                          FStarC_Syntax_Util.type_with_u
                            (FStarC_Syntax_Syntax.U_name u) in
                        FStarC_Syntax_Syntax.gen_bv "a"
                          FStar_Pervasives_Native.None uu___1 in
                      FStarC_Syntax_Syntax.mk_binder uu___ in
                    let rest_bs =
                      let uu___ =
                        let uu___1 = FStarC_Syntax_Subst.compress ite_ty in
                        uu___1.FStarC_Syntax_Syntax.n in
                      match uu___ with
                      | FStarC_Syntax_Syntax.Tm_arrow
                          { FStarC_Syntax_Syntax.bs1 = bs;
                            FStarC_Syntax_Syntax.comp = uu___1;_}
                          when
                          (FStarC_Compiler_List.length bs) >=
                            (Prims.of_int (4))
                          ->
                          let uu___2 = FStarC_Syntax_Subst.open_binders bs in
                          (match uu___2 with
                           | { FStarC_Syntax_Syntax.binder_bv = a;
                               FStarC_Syntax_Syntax.binder_qual = uu___3;
                               FStarC_Syntax_Syntax.binder_positivity =
                                 uu___4;
                               FStarC_Syntax_Syntax.binder_attrs = uu___5;_}::bs1
                               ->
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 =
                                     let uu___9 =
                                       FStarC_Syntax_Syntax.bv_to_name
                                         a_b.FStarC_Syntax_Syntax.binder_bv in
                                     (a, uu___9) in
                                   FStarC_Syntax_Syntax.NT uu___8 in
                                 [uu___7] in
                               let uu___7 =
                                 let uu___8 =
                                   FStarC_Compiler_List.splitAt
                                     ((FStarC_Compiler_List.length bs1) -
                                        (Prims.of_int (3))) bs1 in
                                 FStar_Pervasives_Native.fst uu___8 in
                               FStarC_Syntax_Subst.subst_binders uu___6
                                 uu___7)
                      | uu___1 ->
                          let uu___2 =
                            let uu___3 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_term ite_ty in
                            FStarC_Compiler_Util.format2
                              "Type of %s is not an arrow with >= 4 binders (%s)"
                              ite_name uu___3 in
                          FStarC_Errors.raise_error
                            FStarC_Class_HasRange.hasRange_range r
                            FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                            (Obj.magic
                               FStarC_Errors_Msg.is_error_message_string)
                            (Obj.magic uu___2) in
                    let uu___ =
                      let uu___1 =
                        let uu___2 =
                          FStarC_TypeChecker_Env.push_binders env (a_b ::
                            rest_bs) in
                        let uu___3 =
                          FStarC_Syntax_Syntax.bv_to_name
                            a_b.FStarC_Syntax_Syntax.binder_bv in
                        FStarC_TypeChecker_Util.fresh_effect_repr uu___2 r
                          eff_name sig_ts
                          (FStar_Pervasives_Native.Some repr_ts)
                          (FStarC_Syntax_Syntax.U_name u) uu___3 in
                      match uu___1 with
                      | (repr, g) ->
                          let uu___2 =
                            let uu___3 =
                              FStarC_Syntax_Syntax.gen_bv "f"
                                FStar_Pervasives_Native.None repr in
                            FStarC_Syntax_Syntax.mk_binder uu___3 in
                          (uu___2, g) in
                    match uu___ with
                    | (f, guard_f) ->
                        let uu___1 =
                          let uu___2 =
                            let uu___3 =
                              FStarC_TypeChecker_Env.push_binders env (a_b ::
                                rest_bs) in
                            let uu___4 =
                              FStarC_Syntax_Syntax.bv_to_name
                                a_b.FStarC_Syntax_Syntax.binder_bv in
                            FStarC_TypeChecker_Util.fresh_effect_repr uu___3
                              r eff_name sig_ts
                              (FStar_Pervasives_Native.Some repr_ts)
                              (FStarC_Syntax_Syntax.U_name u) uu___4 in
                          match uu___2 with
                          | (repr, g) ->
                              let uu___3 =
                                let uu___4 =
                                  FStarC_Syntax_Syntax.gen_bv "g"
                                    FStar_Pervasives_Native.None repr in
                                FStarC_Syntax_Syntax.mk_binder uu___4 in
                              (uu___3, g) in
                        (match uu___1 with
                         | (g, guard_g) ->
                             let p =
                               let uu___2 =
                                 FStarC_Syntax_Syntax.gen_bv "p"
                                   FStar_Pervasives_Native.None
                                   FStarC_Syntax_Util.t_bool in
                               FStarC_Syntax_Syntax.mk_binder uu___2 in
                             let uu___2 =
                               let uu___3 =
                                 FStarC_TypeChecker_Env.push_binders env
                                   (FStarC_Compiler_List.op_At (a_b ::
                                      rest_bs) [p]) in
                               let uu___4 =
                                 FStarC_Syntax_Syntax.bv_to_name
                                   a_b.FStarC_Syntax_Syntax.binder_bv in
                               FStarC_TypeChecker_Util.fresh_effect_repr
                                 uu___3 r eff_name sig_ts
                                 (FStar_Pervasives_Native.Some repr_ts)
                                 (FStarC_Syntax_Syntax.U_name u) uu___4 in
                             (match uu___2 with
                              | (body_tm, guard_body) ->
                                  let k =
                                    FStarC_Syntax_Util.abs
                                      (FStarC_Compiler_List.op_At (a_b ::
                                         rest_bs) [f; g; p]) body_tm
                                      FStar_Pervasives_Native.None in
                                  let guard_eq =
                                    let uu___3 =
                                      FStarC_TypeChecker_Rel.teq_nosmt env
                                        ite_tm k in
                                    match uu___3 with
                                    | FStar_Pervasives_Native.None ->
                                        let uu___4 =
                                          let uu___5 =
                                            FStarC_Class_Show.show
                                              FStarC_Syntax_Print.showable_term
                                              ite_tm in
                                          FStarC_Compiler_Util.format2
                                            "Unexpected term for %s (%s)\n"
                                            ite_name uu___5 in
                                        FStarC_Errors.raise_error
                                          FStarC_Class_HasRange.hasRange_range
                                          r
                                          FStarC_Errors_Codes.Fatal_UnexpectedEffect
                                          ()
                                          (Obj.magic
                                             FStarC_Errors_Msg.is_error_message_string)
                                          (Obj.magic uu___4)
                                    | FStar_Pervasives_Native.Some g1 -> g1 in
                                  ((let uu___4 =
                                      FStarC_TypeChecker_Env.conj_guards
                                        [guard_f;
                                        guard_g;
                                        guard_body;
                                        guard_eq] in
                                    FStarC_TypeChecker_Rel.force_trivial_guard
                                      env uu___4);
                                   (let k1 =
                                      let uu___4 =
                                        FStarC_TypeChecker_Normalize.remove_uvar_solutions
                                          env k in
                                      FStarC_Syntax_Subst.compress uu___4 in
                                    let kopt =
                                      ite_combinator_kind env eff_name sig_ts
                                        repr_ts u k1 num_effect_params in
                                    let kind =
                                      match kopt with
                                      | FStar_Pervasives_Native.None ->
                                          (log_ad_hoc_combinator_warning
                                             ite_name r;
                                           FStarC_Syntax_Syntax.Ad_hoc_combinator)
                                      | FStar_Pervasives_Native.Some k2 -> k2 in
                                    (let uu___5 =
                                       (FStarC_Compiler_Debug.medium ()) ||
                                         (FStarC_Compiler_Effect.op_Bang
                                            dbg_LayeredEffectsTc) in
                                     if uu___5
                                     then
                                       let uu___6 =
                                         FStarC_Class_Show.show
                                           FStarC_Syntax_Syntax.showable_indexed_effect_combinator_kind
                                           kind in
                                       FStarC_Compiler_Util.print2
                                         "Ite %s has %s kind\n" ite_name
                                         uu___6
                                     else ());
                                    (k1, kind)))))
let (validate_indexed_effect_close_shape :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Syntax_Syntax.tscheme ->
        FStarC_Syntax_Syntax.tscheme ->
          FStarC_Syntax_Syntax.univ_name ->
            FStarC_Syntax_Syntax.univ_name ->
              FStarC_Syntax_Syntax.term ->
                Prims.int ->
                  FStarC_Compiler_Range_Type.range ->
                    FStarC_Syntax_Syntax.term)
  =
  fun env ->
    fun eff_name ->
      fun sig_ts ->
        fun repr_ts ->
          fun u_a ->
            fun u_b ->
              fun close_tm ->
                fun num_effect_params ->
                  fun r ->
                    let close_name =
                      let uu___ = FStarC_Ident.string_of_lid eff_name in
                      FStarC_Compiler_Util.format1 "close_%s" uu___ in
                    let b_b =
                      let uu___ =
                        let uu___1 =
                          FStarC_Syntax_Util.type_with_u
                            (FStarC_Syntax_Syntax.U_name u_b) in
                        FStarC_Syntax_Syntax.gen_bv "b"
                          FStar_Pervasives_Native.None uu___1 in
                      FStarC_Syntax_Syntax.mk_binder uu___ in
                    let uu___ =
                      let uu___1 =
                        let uu___2 =
                          let uu___3 =
                            FStarC_TypeChecker_Env.inst_tscheme_with sig_ts
                              [FStarC_Syntax_Syntax.U_name u_a] in
                          FStar_Pervasives_Native.snd uu___3 in
                        FStarC_Syntax_Util.arrow_formals uu___2 in
                      FStar_Pervasives_Native.fst uu___1 in
                    match uu___ with
                    | a_b::sig_bs ->
                        let uu___1 =
                          FStarC_Compiler_List.splitAt num_effect_params
                            sig_bs in
                        (match uu___1 with
                         | (eff_params_bs, sig_bs1) ->
                             let bs =
                               FStarC_Compiler_List.map
                                 (fun b ->
                                    let x_b =
                                      let uu___2 =
                                        let uu___3 =
                                          FStarC_Syntax_Syntax.bv_to_name
                                            b_b.FStarC_Syntax_Syntax.binder_bv in
                                        FStarC_Syntax_Syntax.gen_bv "x"
                                          FStar_Pervasives_Native.None uu___3 in
                                      FStarC_Syntax_Syntax.mk_binder uu___2 in
                                    let uu___2 =
                                      let uu___3 =
                                        b.FStarC_Syntax_Syntax.binder_bv in
                                      let uu___4 =
                                        let uu___5 =
                                          FStarC_Syntax_Syntax.mk_Total
                                            (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                        FStarC_Syntax_Util.arrow [x_b] uu___5 in
                                      {
                                        FStarC_Syntax_Syntax.ppname =
                                          (uu___3.FStarC_Syntax_Syntax.ppname);
                                        FStarC_Syntax_Syntax.index =
                                          (uu___3.FStarC_Syntax_Syntax.index);
                                        FStarC_Syntax_Syntax.sort = uu___4
                                      } in
                                    {
                                      FStarC_Syntax_Syntax.binder_bv = uu___2;
                                      FStarC_Syntax_Syntax.binder_qual =
                                        (b.FStarC_Syntax_Syntax.binder_qual);
                                      FStarC_Syntax_Syntax.binder_positivity
                                        =
                                        (b.FStarC_Syntax_Syntax.binder_positivity);
                                      FStarC_Syntax_Syntax.binder_attrs =
                                        (b.FStarC_Syntax_Syntax.binder_attrs)
                                    }) sig_bs1 in
                             let f_b =
                               let uu___2 =
                                 FStarC_TypeChecker_Env.inst_tscheme_with
                                   repr_ts [FStarC_Syntax_Syntax.U_name u_a] in
                               match uu___2 with
                               | (uu___3, repr_t) ->
                                   let x_b =
                                     let uu___4 =
                                       let uu___5 =
                                         FStarC_Syntax_Syntax.bv_to_name
                                           b_b.FStarC_Syntax_Syntax.binder_bv in
                                       FStarC_Syntax_Syntax.gen_bv "x"
                                         FStar_Pervasives_Native.None uu___5 in
                                     FStarC_Syntax_Syntax.mk_binder uu___4 in
                                   let is_args =
                                     FStarC_Compiler_List.map
                                       (fun uu___4 ->
                                          match uu___4 with
                                          | {
                                              FStarC_Syntax_Syntax.binder_bv
                                                = binder_bv;
                                              FStarC_Syntax_Syntax.binder_qual
                                                = uu___5;
                                              FStarC_Syntax_Syntax.binder_positivity
                                                = uu___6;
                                              FStarC_Syntax_Syntax.binder_attrs
                                                = uu___7;_}
                                              ->
                                              let uu___8 =
                                                let uu___9 =
                                                  FStarC_Syntax_Syntax.bv_to_name
                                                    binder_bv in
                                                let uu___10 =
                                                  let uu___11 =
                                                    let uu___12 =
                                                      FStarC_Syntax_Syntax.bv_to_name
                                                        x_b.FStarC_Syntax_Syntax.binder_bv in
                                                    FStarC_Syntax_Syntax.as_arg
                                                      uu___12 in
                                                  [uu___11] in
                                                FStarC_Syntax_Syntax.mk_Tm_app
                                                  uu___9 uu___10
                                                  FStarC_Compiler_Range_Type.dummyRange in
                                              FStarC_Syntax_Syntax.as_arg
                                                uu___8) bs in
                                   let repr_app =
                                     let uu___4 =
                                       let uu___5 =
                                         let uu___6 =
                                           FStarC_Syntax_Syntax.bv_to_name
                                             a_b.FStarC_Syntax_Syntax.binder_bv in
                                         FStarC_Syntax_Syntax.as_arg uu___6 in
                                       uu___5 :: is_args in
                                     FStarC_Syntax_Syntax.mk_Tm_app repr_t
                                       uu___4
                                       FStarC_Compiler_Range_Type.dummyRange in
                                   let f_sort =
                                     let uu___4 =
                                       FStarC_Syntax_Syntax.mk_Total repr_app in
                                     FStarC_Syntax_Util.arrow [x_b] uu___4 in
                                   let uu___4 =
                                     FStarC_Syntax_Syntax.gen_bv "f"
                                       FStar_Pervasives_Native.None f_sort in
                                   FStarC_Syntax_Syntax.mk_binder uu___4 in
                             let env1 =
                               FStarC_TypeChecker_Env.push_binders env (a_b
                                 :: b_b ::
                                 (FStarC_Compiler_List.op_At eff_params_bs bs)) in
                             let uu___2 =
                               let uu___3 =
                                 FStarC_Syntax_Syntax.bv_to_name
                                   a_b.FStarC_Syntax_Syntax.binder_bv in
                               FStarC_TypeChecker_Util.fresh_effect_repr env1
                                 r eff_name sig_ts
                                 (FStar_Pervasives_Native.Some repr_ts)
                                 (FStarC_Syntax_Syntax.U_name u_a) uu___3 in
                             (match uu___2 with
                              | (body_tm, g_body) ->
                                  let k =
                                    FStarC_Syntax_Util.abs (a_b :: b_b ::
                                      (FStarC_Compiler_List.op_At
                                         eff_params_bs
                                         (FStarC_Compiler_List.op_At bs [f_b])))
                                      body_tm FStar_Pervasives_Native.None in
                                  let g_eq =
                                    let uu___3 =
                                      FStarC_TypeChecker_Rel.teq_nosmt env1
                                        close_tm k in
                                    match uu___3 with
                                    | FStar_Pervasives_Native.None ->
                                        let uu___4 =
                                          let uu___5 =
                                            FStarC_Class_Show.show
                                              FStarC_Syntax_Print.showable_term
                                              close_tm in
                                          FStarC_Compiler_Util.format2
                                            "Unexpected term for %s (%s)\n"
                                            close_name uu___5 in
                                        FStarC_Errors.raise_error
                                          FStarC_Class_HasRange.hasRange_range
                                          r
                                          FStarC_Errors_Codes.Fatal_UnexpectedEffect
                                          ()
                                          (Obj.magic
                                             FStarC_Errors_Msg.is_error_message_string)
                                          (Obj.magic uu___4)
                                    | FStar_Pervasives_Native.Some g -> g in
                                  ((let uu___4 =
                                      FStarC_TypeChecker_Env.conj_guard
                                        g_body g_eq in
                                    FStarC_TypeChecker_Rel.force_trivial_guard
                                      env1 uu___4);
                                   (let uu___4 =
                                      FStarC_TypeChecker_Normalize.remove_uvar_solutions
                                        env1 k in
                                    FStarC_Syntax_Subst.compress uu___4))))
let (lift_combinator_kind :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Syntax_Syntax.tscheme ->
        FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ->
          FStarC_Syntax_Syntax.univ_name ->
            FStarC_Syntax_Syntax.typ ->
              FStarC_Syntax_Syntax.indexed_effect_binder_kind Prims.list
                FStar_Pervasives_Native.option)
  =
  fun env ->
    fun m_eff_name ->
      fun m_sig_ts ->
        fun m_repr_ts ->
          fun u ->
            fun k ->
              let uu___ = FStarC_Syntax_Util.arrow_formals k in
              match uu___ with
              | (a_b::rest_bs, uu___1) ->
                  let uu___2 =
                    let f_sig_bs =
                      let uu___3 =
                        FStarC_TypeChecker_Env.inst_tscheme_with m_sig_ts
                          [FStarC_Syntax_Syntax.U_name u] in
                      match uu___3 with
                      | (uu___4, sig1) ->
                          let uu___5 =
                            let uu___6 =
                              FStarC_Syntax_Util.arrow_formals sig1 in
                            FStar_Pervasives_Native.fst uu___6 in
                          (match uu___5 with
                           | a::bs ->
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 =
                                     let uu___9 =
                                       FStarC_Syntax_Syntax.bv_to_name
                                         a_b.FStarC_Syntax_Syntax.binder_bv in
                                     ((a.FStarC_Syntax_Syntax.binder_bv),
                                       uu___9) in
                                   FStarC_Syntax_Syntax.NT uu___8 in
                                 [uu___7] in
                               FStarC_Syntax_Subst.subst_binders uu___6 bs) in
                    let uu___3 =
                      if
                        (FStarC_Compiler_List.length rest_bs) <
                          (FStarC_Compiler_List.length f_sig_bs)
                      then FStar_Pervasives_Native.None
                      else
                        (let uu___5 =
                           FStarC_Compiler_List.splitAt
                             (FStarC_Compiler_List.length f_sig_bs) rest_bs in
                         FStar_Pervasives_Native.Some uu___5) in
                    op_let_Question uu___3
                      (fun uu___4 ->
                         match uu___4 with
                         | (f_bs, rest_bs1) ->
                             let uu___5 = eq_binders env f_sig_bs f_bs in
                             op_let_Question uu___5
                               (fun f_bs_kinds ->
                                  FStar_Pervasives_Native.Some
                                    (f_bs, f_bs_kinds, rest_bs1))) in
                  op_let_Question uu___2
                    (fun uu___3 ->
                       match uu___3 with
                       | (f_bs, f_bs_kinds, rest_bs1) ->
                           let uu___4 =
                             if
                               (FStarC_Compiler_List.length rest_bs1) >=
                                 Prims.int_one
                             then
                               let uu___5 =
                                 FStarC_Compiler_List.splitAt
                                   ((FStarC_Compiler_List.length rest_bs1) -
                                      Prims.int_one) rest_bs1 in
                               match uu___5 with
                               | (rest_bs2, f_b::[]) ->
                                   FStar_Pervasives_Native.Some
                                     (rest_bs2, f_b)
                             else FStar_Pervasives_Native.None in
                           op_let_Question uu___4
                             (fun uu___5 ->
                                match uu___5 with
                                | (rest_bs2, f_b) ->
                                    let uu___6 =
                                      let expected_f_b_sort =
                                        match m_repr_ts with
                                        | FStar_Pervasives_Native.Some
                                            repr_ts ->
                                            let uu___7 =
                                              FStarC_TypeChecker_Env.inst_tscheme_with
                                                repr_ts
                                                [FStarC_Syntax_Syntax.U_name
                                                   u] in
                                            (match uu___7 with
                                             | (uu___8, t) ->
                                                 let uu___9 =
                                                   let uu___10 =
                                                     let uu___11 =
                                                       FStarC_Syntax_Syntax.bv_to_name
                                                         a_b.FStarC_Syntax_Syntax.binder_bv in
                                                     FStarC_Syntax_Syntax.as_arg
                                                       uu___11 in
                                                   let uu___11 =
                                                     FStarC_Compiler_List.map
                                                       (fun uu___12 ->
                                                          match uu___12 with
                                                          | {
                                                              FStarC_Syntax_Syntax.binder_bv
                                                                = b;
                                                              FStarC_Syntax_Syntax.binder_qual
                                                                = uu___13;
                                                              FStarC_Syntax_Syntax.binder_positivity
                                                                = uu___14;
                                                              FStarC_Syntax_Syntax.binder_attrs
                                                                = uu___15;_}
                                                              ->
                                                              let uu___16 =
                                                                FStarC_Syntax_Syntax.bv_to_name
                                                                  b in
                                                              FStarC_Syntax_Syntax.as_arg
                                                                uu___16) f_bs in
                                                   uu___10 :: uu___11 in
                                                 FStarC_Syntax_Syntax.mk_Tm_app
                                                   t uu___9
                                                   FStarC_Compiler_Range_Type.dummyRange)
                                        | FStar_Pervasives_Native.None ->
                                            let uu___7 =
                                              let uu___8 =
                                                FStarC_Syntax_Syntax.null_binder
                                                  FStarC_Syntax_Syntax.t_unit in
                                              [uu___8] in
                                            let uu___8 =
                                              let uu___9 =
                                                let uu___10 =
                                                  FStarC_Syntax_Syntax.bv_to_name
                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                let uu___11 =
                                                  FStarC_Compiler_List.map
                                                    (fun b ->
                                                       let uu___12 =
                                                         FStarC_Syntax_Syntax.bv_to_name
                                                           b.FStarC_Syntax_Syntax.binder_bv in
                                                       FStarC_Syntax_Syntax.as_arg
                                                         uu___12) f_bs in
                                                {
                                                  FStarC_Syntax_Syntax.comp_univs
                                                    =
                                                    [FStarC_Syntax_Syntax.U_name
                                                       u];
                                                  FStarC_Syntax_Syntax.effect_name
                                                    = m_eff_name;
                                                  FStarC_Syntax_Syntax.result_typ
                                                    = uu___10;
                                                  FStarC_Syntax_Syntax.effect_args
                                                    = uu___11;
                                                  FStarC_Syntax_Syntax.flags
                                                    = []
                                                } in
                                              FStarC_Syntax_Syntax.mk_Comp
                                                uu___9 in
                                            FStarC_Syntax_Util.arrow uu___7
                                              uu___8 in
                                      let uu___7 =
                                        let uu___8 =
                                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                            env
                                            (f_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                            expected_f_b_sort in
                                        uu___8 =
                                          FStarC_TypeChecker_TermEqAndSimplify.Equal in
                                      if uu___7
                                      then FStar_Pervasives_Native.Some ()
                                      else FStar_Pervasives_Native.None in
                                    op_let_Question uu___6
                                      (fun _f_b_ok_ ->
                                         let rest_kinds =
                                           FStarC_Compiler_List.map
                                             (fun uu___7 ->
                                                FStarC_Syntax_Syntax.Ad_hoc_binder)
                                             rest_bs2 in
                                         FStar_Pervasives_Native.Some
                                           (FStarC_Compiler_List.op_At
                                              [FStarC_Syntax_Syntax.Type_binder]
                                              (FStarC_Compiler_List.op_At
                                                 f_bs_kinds
                                                 (FStarC_Compiler_List.op_At
                                                    rest_kinds
                                                    [FStarC_Syntax_Syntax.Repr_binder]))))))
let (validate_indexed_effect_lift_shape :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Ident.lident ->
        FStarC_Syntax_Syntax.univ_name ->
          FStarC_Syntax_Syntax.typ ->
            FStarC_Compiler_Range_Type.range ->
              (FStarC_Syntax_Syntax.typ *
                FStarC_Syntax_Syntax.indexed_effect_combinator_kind))
  =
  fun env ->
    fun m_eff_name ->
      fun n_eff_name ->
        fun u ->
          fun lift_t ->
            fun r ->
              let lift_name =
                let uu___ = FStarC_Ident.string_of_lid m_eff_name in
                let uu___1 = FStarC_Ident.string_of_lid n_eff_name in
                FStarC_Compiler_Util.format2 "%s ~> %s" uu___ uu___1 in
              let lift_t_shape_error s =
                FStarC_Compiler_Util.format2
                  "Unexpected shape of lift %s, reason:%s" lift_name s in
              let uu___ =
                let uu___1 =
                  FStarC_TypeChecker_Env.get_effect_decl env m_eff_name in
                let uu___2 =
                  FStarC_TypeChecker_Env.get_effect_decl env n_eff_name in
                (uu___1, uu___2) in
              match uu___ with
              | (m_ed, n_ed) ->
                  let a_b =
                    let uu___1 =
                      let uu___2 =
                        FStarC_Syntax_Util.type_with_u
                          (FStarC_Syntax_Syntax.U_name u) in
                      FStarC_Syntax_Syntax.gen_bv "a"
                        FStar_Pervasives_Native.None uu___2 in
                    FStarC_Syntax_Syntax.mk_binder uu___1 in
                  let uu___1 =
                    let uu___2 =
                      let uu___3 = FStarC_Syntax_Subst.compress lift_t in
                      uu___3.FStarC_Syntax_Syntax.n in
                    match uu___2 with
                    | FStarC_Syntax_Syntax.Tm_arrow
                        { FStarC_Syntax_Syntax.bs1 = bs;
                          FStarC_Syntax_Syntax.comp = c;_}
                        when
                        (FStarC_Compiler_List.length bs) >=
                          (Prims.of_int (2))
                        ->
                        let uu___3 = FStarC_Syntax_Subst.open_binders bs in
                        (match uu___3 with
                         | { FStarC_Syntax_Syntax.binder_bv = a;
                             FStarC_Syntax_Syntax.binder_qual = uu___4;
                             FStarC_Syntax_Syntax.binder_positivity = uu___5;
                             FStarC_Syntax_Syntax.binder_attrs = uu___6;_}::bs1
                             ->
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 =
                                   let uu___10 =
                                     let uu___11 =
                                       FStarC_Syntax_Syntax.bv_to_name
                                         a_b.FStarC_Syntax_Syntax.binder_bv in
                                     (a, uu___11) in
                                   FStarC_Syntax_Syntax.NT uu___10 in
                                 [uu___9] in
                               let uu___9 =
                                 let uu___10 =
                                   FStarC_Compiler_List.splitAt
                                     ((FStarC_Compiler_List.length bs1) -
                                        Prims.int_one) bs1 in
                                 FStar_Pervasives_Native.fst uu___10 in
                               FStarC_Syntax_Subst.subst_binders uu___8
                                 uu___9 in
                             let uu___8 =
                               FStarC_TypeChecker_Env.norm_eff_name env
                                 (FStarC_Syntax_Util.comp_effect_name c) in
                             (uu___7, uu___8))
                    | uu___3 ->
                        let uu___4 =
                          lift_t_shape_error
                            "either not an arrow, or not enough binders" in
                        FStarC_Errors.raise_error
                          FStarC_Class_HasRange.hasRange_range r
                          FStarC_Errors_Codes.Fatal_UnexpectedExpressionType
                          ()
                          (Obj.magic
                             FStarC_Errors_Msg.is_error_message_string)
                          (Obj.magic uu___4) in
                  (match uu___1 with
                   | (rest_bs, lift_eff) ->
                       ((let uu___3 =
                           let uu___4 =
                             (FStarC_Ident.lid_equals lift_eff
                                FStarC_Parser_Const.effect_PURE_lid)
                               ||
                               ((FStarC_Ident.lid_equals lift_eff
                                   FStarC_Parser_Const.effect_GHOST_lid)
                                  &&
                                  (FStarC_TypeChecker_Env.is_erasable_effect
                                     env m_eff_name)) in
                           Prims.op_Negation uu___4 in
                         if uu___3
                         then
                           let uu___4 =
                             lift_t_shape_error
                               "the lift combinator has an unexpected effect: it must either be PURE or if the source effect is erasable then may be GHOST" in
                           FStarC_Errors.raise_error
                             FStarC_Class_HasRange.hasRange_range r
                             FStarC_Errors_Codes.Fatal_UnexpectedExpressionType
                             ()
                             (Obj.magic
                                FStarC_Errors_Msg.is_error_message_string)
                             (Obj.magic uu___4)
                         else ());
                        (let uu___3 =
                           let uu___4 =
                             let uu___5 =
                               FStarC_TypeChecker_Env.push_binders env (a_b
                                 :: rest_bs) in
                             let uu___6 =
                               FStarC_Syntax_Util.effect_sig_ts
                                 m_ed.FStarC_Syntax_Syntax.signature in
                             let uu___7 =
                               FStarC_Syntax_Util.get_eff_repr m_ed in
                             let uu___8 =
                               FStarC_Syntax_Syntax.bv_to_name
                                 a_b.FStarC_Syntax_Syntax.binder_bv in
                             FStarC_TypeChecker_Util.fresh_effect_repr uu___5
                               r m_eff_name uu___6 uu___7
                               (FStarC_Syntax_Syntax.U_name u) uu___8 in
                           match uu___4 with
                           | (repr, g) ->
                               let uu___5 =
                                 let uu___6 =
                                   FStarC_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr in
                                 FStarC_Syntax_Syntax.mk_binder uu___6 in
                               (uu___5, g) in
                         match uu___3 with
                         | (f, guard_f) ->
                             let uu___4 =
                               let uu___5 =
                                 FStarC_TypeChecker_Env.push_binders env (a_b
                                   :: rest_bs) in
                               let uu___6 =
                                 FStarC_Syntax_Util.effect_sig_ts
                                   n_ed.FStarC_Syntax_Syntax.signature in
                               let uu___7 =
                                 FStarC_Syntax_Util.get_eff_repr n_ed in
                               let uu___8 =
                                 FStarC_Syntax_Syntax.bv_to_name
                                   a_b.FStarC_Syntax_Syntax.binder_bv in
                               FStarC_TypeChecker_Util.fresh_effect_repr
                                 uu___5 r n_eff_name uu___6 uu___7
                                 (FStarC_Syntax_Syntax.U_name u) uu___8 in
                             (match uu___4 with
                              | (ret_t, guard_ret_t) ->
                                  let uu___5 =
                                    let uu___6 =
                                      FStarC_TypeChecker_Env.push_binders env
                                        (a_b :: rest_bs) in
                                    let uu___7 =
                                      FStarC_Compiler_Util.format1
                                        "implicit for pure_wp in typechecking lift %s"
                                        lift_name in
                                    pure_wp_uvar uu___6 ret_t uu___7 r in
                                  (match uu___5 with
                                   | (pure_wp_uvar1, guard_wp) ->
                                       let c =
                                         let uu___6 =
                                           let uu___7 =
                                             let uu___8 =
                                               FStarC_TypeChecker_Env.new_u_univ
                                                 () in
                                             [uu___8] in
                                           let uu___8 =
                                             let uu___9 =
                                               FStarC_Syntax_Syntax.as_arg
                                                 pure_wp_uvar1 in
                                             [uu___9] in
                                           {
                                             FStarC_Syntax_Syntax.comp_univs
                                               = uu___7;
                                             FStarC_Syntax_Syntax.effect_name
                                               = lift_eff;
                                             FStarC_Syntax_Syntax.result_typ
                                               = ret_t;
                                             FStarC_Syntax_Syntax.effect_args
                                               = uu___8;
                                             FStarC_Syntax_Syntax.flags = []
                                           } in
                                         FStarC_Syntax_Syntax.mk_Comp uu___6 in
                                       let k =
                                         FStarC_Syntax_Util.arrow
                                           (FStarC_Compiler_List.op_At (a_b
                                              :: rest_bs) [f]) c in
                                       let guard_eq =
                                         let uu___6 =
                                           FStarC_TypeChecker_Rel.teq_nosmt
                                             env lift_t k in
                                         match uu___6 with
                                         | FStar_Pervasives_Native.None ->
                                             let uu___7 =
                                               let uu___8 =
                                                 FStarC_Class_Show.show
                                                   FStarC_Syntax_Print.showable_term
                                                   lift_t in
                                               FStarC_Compiler_Util.format2
                                                 "Unexpected type of %s (%s)\n"
                                                 lift_name uu___8 in
                                             FStarC_Errors.raise_error
                                               FStarC_Class_HasRange.hasRange_range
                                               r
                                               FStarC_Errors_Codes.Fatal_UnexpectedEffect
                                               ()
                                               (Obj.magic
                                                  FStarC_Errors_Msg.is_error_message_string)
                                               (Obj.magic uu___7)
                                         | FStar_Pervasives_Native.Some g ->
                                             g in
                                       ((let uu___7 =
                                           FStarC_TypeChecker_Env.conj_guards
                                             [guard_f;
                                             guard_ret_t;
                                             guard_wp;
                                             guard_eq] in
                                         FStarC_TypeChecker_Rel.force_trivial_guard
                                           env uu___7);
                                        (let k1 =
                                           let uu___7 =
                                             FStarC_TypeChecker_Normalize.remove_uvar_solutions
                                               env k in
                                           FStarC_Syntax_Subst.compress
                                             uu___7 in
                                         let lopt =
                                           let uu___7 =
                                             FStarC_Syntax_Util.effect_sig_ts
                                               m_ed.FStarC_Syntax_Syntax.signature in
                                           let uu___8 =
                                             FStarC_Syntax_Util.get_eff_repr
                                               m_ed in
                                           lift_combinator_kind env
                                             m_eff_name uu___7 uu___8 u k1 in
                                         let kind =
                                           match lopt with
                                           | FStar_Pervasives_Native.None ->
                                               (log_ad_hoc_combinator_warning
                                                  lift_name r;
                                                FStarC_Syntax_Syntax.Ad_hoc_combinator)
                                           | FStar_Pervasives_Native.Some l
                                               ->
                                               FStarC_Syntax_Syntax.Substitutive_combinator
                                                 l in
                                         (let uu___8 =
                                            (FStarC_Compiler_Debug.medium ())
                                              ||
                                              (FStarC_Compiler_Effect.op_Bang
                                                 dbg_LayeredEffectsTc) in
                                          if uu___8
                                          then
                                            let uu___9 =
                                              FStarC_Class_Show.show
                                                FStarC_Syntax_Syntax.showable_indexed_effect_combinator_kind
                                                kind in
                                            FStarC_Compiler_Util.print2
                                              "Lift %s has %s kind\n"
                                              lift_name uu___9
                                          else ());
                                         (k1, kind))))))))
let (tc_layered_eff_decl :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.eff_decl ->
      FStarC_Syntax_Syntax.qualifier Prims.list ->
        FStarC_Syntax_Syntax.attribute Prims.list ->
          FStarC_Syntax_Syntax.eff_decl)
  =
  fun env0 ->
    fun ed ->
      fun quals ->
        fun attrs ->
          let uu___ =
            let uu___1 =
              FStarC_Ident.string_of_lid ed.FStarC_Syntax_Syntax.mname in
            FStarC_Compiler_Util.format1
              "While checking layered effect definition `%s`" uu___1 in
          FStarC_Errors.with_ctx uu___
            (fun uu___1 ->
               (let uu___3 =
                  FStarC_Compiler_Effect.op_Bang dbg_LayeredEffectsTc in
                if uu___3
                then
                  let uu___4 =
                    FStarC_Class_Show.show
                      FStarC_Syntax_Print.showable_eff_decl ed in
                  FStarC_Compiler_Util.print1
                    "Typechecking layered effect: \n\t%s\n" uu___4
                else ());
               if
                 ((FStarC_Compiler_List.length ed.FStarC_Syntax_Syntax.univs)
                    <> Prims.int_zero)
                   ||
                   ((FStarC_Compiler_List.length
                       ed.FStarC_Syntax_Syntax.binders)
                      <> Prims.int_zero)
               then
                 (let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        FStarC_Ident.string_of_lid
                          ed.FStarC_Syntax_Syntax.mname in
                      Prims.strcat uu___6 ")" in
                    Prims.strcat
                      "Binders are not supported for layered effects ("
                      uu___5 in
                  FStarC_Errors.raise_error FStarC_Ident.hasrange_lident
                    ed.FStarC_Syntax_Syntax.mname
                    FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                    (Obj.magic uu___4))
               else ();
               (let log_combinator s uu___4 =
                  match uu___4 with
                  | (us, t, ty) ->
                      let uu___5 =
                        FStarC_Compiler_Effect.op_Bang dbg_LayeredEffectsTc in
                      if uu___5
                      then
                        let uu___6 =
                          FStarC_Ident.string_of_lid
                            ed.FStarC_Syntax_Syntax.mname in
                        let uu___7 =
                          FStarC_Syntax_Print.tscheme_to_string (us, t) in
                        let uu___8 =
                          FStarC_Syntax_Print.tscheme_to_string (us, ty) in
                        FStarC_Compiler_Util.print4
                          "Typechecked %s:%s = %s:%s\n" uu___6 s uu___7
                          uu___8
                      else () in
                let fresh_a_and_u_a a =
                  let uu___4 = FStarC_Syntax_Util.type_u () in
                  match uu___4 with
                  | (t, u) ->
                      let uu___5 =
                        let uu___6 =
                          FStarC_Syntax_Syntax.gen_bv a
                            FStar_Pervasives_Native.None t in
                        FStarC_Syntax_Syntax.mk_binder uu___6 in
                      (uu___5, u) in
                let fresh_x_a x a =
                  let uu___4 =
                    let uu___5 =
                      FStarC_Syntax_Syntax.bv_to_name
                        a.FStarC_Syntax_Syntax.binder_bv in
                    FStarC_Syntax_Syntax.gen_bv x
                      FStar_Pervasives_Native.None uu___5 in
                  FStarC_Syntax_Syntax.mk_binder uu___4 in
                let check_and_gen1 =
                  let uu___4 =
                    FStarC_Ident.string_of_lid ed.FStarC_Syntax_Syntax.mname in
                  check_and_gen env0 uu___4 in
                let uu___4 =
                  let uu___5 =
                    match ed.FStarC_Syntax_Syntax.signature with
                    | FStarC_Syntax_Syntax.Layered_eff_sig (n, ts) -> (n, ts)
                    | uu___6 ->
                        failwith
                          "Impossible (tc_layered_eff_decl with a wp effect sig" in
                  match uu___5 with
                  | (n, sig_ts) ->
                      FStarC_Errors.with_ctx
                        "While checking the effect signature"
                        (fun uu___6 ->
                           let r =
                             (FStar_Pervasives_Native.snd sig_ts).FStarC_Syntax_Syntax.pos in
                           let uu___7 =
                             check_and_gen1 "signature" Prims.int_one sig_ts in
                           match uu___7 with
                           | (sig_us, sig_t, sig_ty) ->
                               let uu___8 =
                                 FStarC_Syntax_Subst.open_univ_vars sig_us
                                   sig_t in
                               (match uu___8 with
                                | (us, t) ->
                                    let env =
                                      FStarC_TypeChecker_Env.push_univ_vars
                                        env0 us in
                                    let uu___9 = fresh_a_and_u_a "a" in
                                    (match uu___9 with
                                     | (a, u) ->
                                         let rest_bs =
                                           let uu___10 =
                                             FStarC_Syntax_Syntax.bv_to_name
                                               a.FStarC_Syntax_Syntax.binder_bv in
                                           FStarC_TypeChecker_Util.layered_effect_indices_as_binders
                                             env r
                                             ed.FStarC_Syntax_Syntax.mname
                                             (sig_us, sig_t) u uu___10 in
                                         let bs = a :: rest_bs in
                                         let k =
                                           let uu___10 =
                                             FStarC_Syntax_Syntax.mk_Total
                                               FStarC_Syntax_Syntax.teff in
                                           FStarC_Syntax_Util.arrow bs
                                             uu___10 in
                                         let g_eq =
                                           FStarC_TypeChecker_Rel.teq env t k in
                                         (FStarC_TypeChecker_Rel.force_trivial_guard
                                            env g_eq;
                                          (let uu___11 =
                                             let uu___12 =
                                               let uu___13 =
                                                 FStarC_TypeChecker_Normalize.remove_uvar_solutions
                                                   env k in
                                               FStarC_Syntax_Subst.close_univ_vars
                                                 us uu___13 in
                                             (sig_us, uu___12, sig_ty) in
                                           (n, uu___11)))))) in
                match uu___4 with
                | (num_effect_params, signature) ->
                    (log_combinator "signature" signature;
                     (let repr =
                        FStarC_Errors.with_ctx
                          "While checking the effect repr"
                          (fun uu___6 ->
                             let repr_ts =
                               let uu___7 =
                                 FStarC_Syntax_Util.get_eff_repr ed in
                               FStarC_Compiler_Util.must uu___7 in
                             let r =
                               (FStar_Pervasives_Native.snd repr_ts).FStarC_Syntax_Syntax.pos in
                             let uu___7 =
                               check_and_gen1 "repr" Prims.int_one repr_ts in
                             match uu___7 with
                             | (repr_us, repr_t, repr_ty) ->
                                 let uu___8 =
                                   FStarC_Syntax_Subst.open_univ_vars repr_us
                                     repr_ty in
                                 (match uu___8 with
                                  | (us, ty) ->
                                      let env =
                                        FStarC_TypeChecker_Env.push_univ_vars
                                          env0 us in
                                      let uu___9 = fresh_a_and_u_a "a" in
                                      (match uu___9 with
                                       | (a, u) ->
                                           let rest_bs =
                                             let signature_ts =
                                               let uu___10 = signature in
                                               match uu___10 with
                                               | (us1, t, uu___11) ->
                                                   (us1, t) in
                                             let uu___10 =
                                               FStarC_Syntax_Syntax.bv_to_name
                                                 a.FStarC_Syntax_Syntax.binder_bv in
                                             FStarC_TypeChecker_Util.layered_effect_indices_as_binders
                                               env r
                                               ed.FStarC_Syntax_Syntax.mname
                                               signature_ts u uu___10 in
                                           let bs = a :: rest_bs in
                                           let k =
                                             let uu___10 =
                                               let uu___11 =
                                                 FStarC_Syntax_Util.type_u () in
                                               match uu___11 with
                                               | (t, u1) ->
                                                   FStarC_Syntax_Syntax.mk_Total
                                                     t in
                                             FStarC_Syntax_Util.arrow bs
                                               uu___10 in
                                           let g =
                                             FStarC_TypeChecker_Rel.teq env
                                               ty k in
                                           (FStarC_TypeChecker_Rel.force_trivial_guard
                                              env g;
                                            (let uu___11 =
                                               let uu___12 =
                                                 FStarC_TypeChecker_Normalize.remove_uvar_solutions
                                                   env k in
                                               FStarC_Syntax_Subst.close_univ_vars
                                                 us uu___12 in
                                             (repr_us, repr_t, uu___11)))))) in
                      log_combinator "repr" repr;
                      (let fresh_repr r env u a_tm =
                         let signature_ts =
                           let uu___7 = signature in
                           match uu___7 with | (us, t, uu___8) -> (us, t) in
                         let repr_ts =
                           let uu___7 = repr in
                           match uu___7 with | (us, t, uu___8) -> (us, t) in
                         FStarC_TypeChecker_Util.fresh_effect_repr env r
                           ed.FStarC_Syntax_Syntax.mname signature_ts
                           (FStar_Pervasives_Native.Some repr_ts) u a_tm in
                       let not_an_arrow_error comb n t r =
                         let uu___7 =
                           let uu___8 =
                             FStarC_Ident.string_of_lid
                               ed.FStarC_Syntax_Syntax.mname in
                           let uu___9 =
                             FStarC_Class_Show.show
                               FStarC_Class_Show.showable_int n in
                           let uu___10 =
                             FStarC_Class_Tagged.tag_of
                               FStarC_Syntax_Syntax.tagged_term t in
                           let uu___11 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_term t in
                           FStarC_Compiler_Util.format5
                             "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                             uu___8 comb uu___9 uu___10 uu___11 in
                         FStarC_Errors.raise_error
                           FStarC_Class_HasRange.hasRange_range r
                           FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                           (Obj.magic
                              FStarC_Errors_Msg.is_error_message_string)
                           (Obj.magic uu___7) in
                       let return_repr =
                         FStarC_Errors.with_ctx
                           "While checking the return combinator"
                           (fun uu___7 ->
                              let return_repr_ts =
                                let uu___8 =
                                  FStarC_Syntax_Util.get_return_repr ed in
                                FStarC_Compiler_Util.must uu___8 in
                              let r =
                                (FStar_Pervasives_Native.snd return_repr_ts).FStarC_Syntax_Syntax.pos in
                              let uu___8 =
                                check_and_gen1 "return_repr" Prims.int_one
                                  return_repr_ts in
                              match uu___8 with
                              | (ret_us, ret_t, ret_ty) ->
                                  let uu___9 =
                                    FStarC_Syntax_Subst.open_univ_vars ret_us
                                      ret_ty in
                                  (match uu___9 with
                                   | (us, ty) ->
                                       let env =
                                         FStarC_TypeChecker_Env.push_univ_vars
                                           env0 us in
                                       let uu___10 = fresh_a_and_u_a "a" in
                                       (match uu___10 with
                                        | (a, u_a) ->
                                            let x_a = fresh_x_a "x" a in
                                            let rest_bs =
                                              let uu___11 =
                                                let uu___12 =
                                                  FStarC_Syntax_Subst.compress
                                                    ty in
                                                uu___12.FStarC_Syntax_Syntax.n in
                                              match uu___11 with
                                              | FStarC_Syntax_Syntax.Tm_arrow
                                                  {
                                                    FStarC_Syntax_Syntax.bs1
                                                      = bs;
                                                    FStarC_Syntax_Syntax.comp
                                                      = uu___12;_}
                                                  when
                                                  (FStarC_Compiler_List.length
                                                     bs)
                                                    >= (Prims.of_int (2))
                                                  ->
                                                  let uu___13 =
                                                    FStarC_Syntax_Subst.open_binders
                                                      bs in
                                                  (match uu___13 with
                                                   | {
                                                       FStarC_Syntax_Syntax.binder_bv
                                                         = a';
                                                       FStarC_Syntax_Syntax.binder_qual
                                                         = uu___14;
                                                       FStarC_Syntax_Syntax.binder_positivity
                                                         = uu___15;
                                                       FStarC_Syntax_Syntax.binder_attrs
                                                         = uu___16;_}::
                                                       {
                                                         FStarC_Syntax_Syntax.binder_bv
                                                           = x';
                                                         FStarC_Syntax_Syntax.binder_qual
                                                           = uu___17;
                                                         FStarC_Syntax_Syntax.binder_positivity
                                                           = uu___18;
                                                         FStarC_Syntax_Syntax.binder_attrs
                                                           = uu___19;_}::bs1
                                                       ->
                                                       let uu___20 =
                                                         let uu___21 =
                                                           let uu___22 =
                                                             let uu___23 =
                                                               FStarC_Syntax_Syntax.bv_to_name
                                                                 x_a.FStarC_Syntax_Syntax.binder_bv in
                                                             (x', uu___23) in
                                                           FStarC_Syntax_Syntax.NT
                                                             uu___22 in
                                                         [uu___21] in
                                                       let uu___21 =
                                                         let uu___22 =
                                                           let uu___23 =
                                                             let uu___24 =
                                                               let uu___25 =
                                                                 FStarC_Syntax_Syntax.bv_to_name
                                                                   a.FStarC_Syntax_Syntax.binder_bv in
                                                               (a', uu___25) in
                                                             FStarC_Syntax_Syntax.NT
                                                               uu___24 in
                                                           [uu___23] in
                                                         FStarC_Syntax_Subst.subst_binders
                                                           uu___22 bs1 in
                                                       FStarC_Syntax_Subst.subst_binders
                                                         uu___20 uu___21)
                                              | uu___12 ->
                                                  not_an_arrow_error "return"
                                                    (Prims.of_int (2)) ty r in
                                            let bs = a :: x_a :: rest_bs in
                                            let uu___11 =
                                              let uu___12 =
                                                FStarC_TypeChecker_Env.push_binders
                                                  env bs in
                                              let uu___13 =
                                                FStarC_Syntax_Syntax.bv_to_name
                                                  a.FStarC_Syntax_Syntax.binder_bv in
                                              fresh_repr r uu___12 u_a
                                                uu___13 in
                                            (match uu___11 with
                                             | (repr1, g) ->
                                                 let k =
                                                   let uu___12 =
                                                     FStarC_Syntax_Syntax.mk_Total
                                                       repr1 in
                                                   FStarC_Syntax_Util.arrow
                                                     bs uu___12 in
                                                 let g_eq =
                                                   FStarC_TypeChecker_Rel.teq
                                                     env ty k in
                                                 ((let uu___13 =
                                                     FStarC_TypeChecker_Env.conj_guard
                                                       g g_eq in
                                                   FStarC_TypeChecker_Rel.force_trivial_guard
                                                     env uu___13);
                                                  (let k1 =
                                                     FStarC_TypeChecker_Normalize.remove_uvar_solutions
                                                       env k in
                                                   let uu___13 =
                                                     FStarC_Syntax_Subst.close_univ_vars
                                                       us k1 in
                                                   (ret_us, ret_t, uu___13))))))) in
                       log_combinator "return_repr" return_repr;
                       (let uu___8 =
                          FStarC_Errors.with_ctx
                            "While checking the bind combinator"
                            (fun uu___9 ->
                               let bind_repr_ts =
                                 let uu___10 =
                                   FStarC_Syntax_Util.get_bind_repr ed in
                                 FStarC_Compiler_Util.must uu___10 in
                               let r =
                                 (FStar_Pervasives_Native.snd bind_repr_ts).FStarC_Syntax_Syntax.pos in
                               let uu___10 =
                                 check_and_gen1 "bind_repr"
                                   (Prims.of_int (2)) bind_repr_ts in
                               match uu___10 with
                               | (bind_us, bind_t, bind_ty) ->
                                   let uu___11 =
                                     FStarC_Syntax_Subst.open_univ_vars
                                       bind_us bind_ty in
                                   (match uu___11 with
                                    | (us, ty) ->
                                        let env =
                                          FStarC_TypeChecker_Env.push_univ_vars
                                            env0 us in
                                        let uu___12 =
                                          let sig_ts =
                                            let uu___13 = signature in
                                            match uu___13 with
                                            | (us1, t, uu___14) -> (us1, t) in
                                          let repr_ts =
                                            let uu___13 = repr in
                                            match uu___13 with
                                            | (us1, t, uu___14) -> (us1, t) in
                                          let uu___13 =
                                            FStarC_Syntax_Util.has_attribute
                                              ed.FStarC_Syntax_Syntax.eff_attrs
                                              FStarC_Parser_Const.bind_has_range_args_attr in
                                          validate_indexed_effect_bind_shape
                                            env ed.FStarC_Syntax_Syntax.mname
                                            ed.FStarC_Syntax_Syntax.mname
                                            ed.FStarC_Syntax_Syntax.mname
                                            sig_ts sig_ts sig_ts
                                            (FStar_Pervasives_Native.Some
                                               repr_ts)
                                            (FStar_Pervasives_Native.Some
                                               repr_ts)
                                            (FStar_Pervasives_Native.Some
                                               repr_ts) us ty r
                                            num_effect_params uu___13 in
                                        (match uu___12 with
                                         | (k, kind) ->
                                             let uu___13 =
                                               let uu___14 =
                                                 FStarC_Syntax_Subst.close_univ_vars
                                                   bind_us k in
                                               (bind_us, bind_t, uu___14) in
                                             (uu___13, kind)))) in
                        match uu___8 with
                        | (bind_repr, bind_kind) ->
                            (log_combinator "bind_repr" bind_repr;
                             (let uu___10 =
                                FStarC_Errors.with_ctx
                                  "While checking the subcomp combinator"
                                  (fun uu___11 ->
                                     let stronger_repr =
                                       let ts =
                                         let uu___12 =
                                           FStarC_Syntax_Util.get_stronger_repr
                                             ed in
                                         FStarC_Compiler_Util.must uu___12 in
                                       let uu___12 =
                                         let uu___13 =
                                           FStarC_Syntax_Subst.compress
                                             (FStar_Pervasives_Native.snd ts) in
                                         uu___13.FStarC_Syntax_Syntax.n in
                                       match uu___12 with
                                       | FStarC_Syntax_Syntax.Tm_unknown ->
                                           let signature_ts =
                                             let uu___13 = signature in
                                             match uu___13 with
                                             | (us, t, uu___14) -> (us, t) in
                                           let uu___13 =
                                             FStarC_TypeChecker_Env.inst_tscheme_with
                                               signature_ts
                                               [FStarC_Syntax_Syntax.U_unknown] in
                                           (match uu___13 with
                                            | (uu___14, signature_t) ->
                                                let uu___15 =
                                                  let uu___16 =
                                                    FStarC_Syntax_Subst.compress
                                                      signature_t in
                                                  uu___16.FStarC_Syntax_Syntax.n in
                                                (match uu___15 with
                                                 | FStarC_Syntax_Syntax.Tm_arrow
                                                     {
                                                       FStarC_Syntax_Syntax.bs1
                                                         = bs;
                                                       FStarC_Syntax_Syntax.comp
                                                         = uu___16;_}
                                                     ->
                                                     let bs1 =
                                                       FStarC_Syntax_Subst.open_binders
                                                         bs in
                                                     let repr_t =
                                                       let repr_ts =
                                                         let uu___17 = repr in
                                                         match uu___17 with
                                                         | (us, t, uu___18)
                                                             -> (us, t) in
                                                       let uu___17 =
                                                         FStarC_TypeChecker_Env.inst_tscheme_with
                                                           repr_ts
                                                           [FStarC_Syntax_Syntax.U_unknown] in
                                                       FStar_Pervasives_Native.snd
                                                         uu___17 in
                                                     let repr_t_applied =
                                                       let uu___17 =
                                                         let uu___18 =
                                                           let uu___19 =
                                                             let uu___20 =
                                                               let uu___21 =
                                                                 FStarC_Compiler_List.map
                                                                   (fun b ->
                                                                    b.FStarC_Syntax_Syntax.binder_bv)
                                                                   bs1 in
                                                               FStarC_Compiler_List.map
                                                                 FStarC_Syntax_Syntax.bv_to_name
                                                                 uu___21 in
                                                             FStarC_Compiler_List.map
                                                               FStarC_Syntax_Syntax.as_arg
                                                               uu___20 in
                                                           {
                                                             FStarC_Syntax_Syntax.hd
                                                               = repr_t;
                                                             FStarC_Syntax_Syntax.args
                                                               = uu___19
                                                           } in
                                                         FStarC_Syntax_Syntax.Tm_app
                                                           uu___18 in
                                                       let uu___18 =
                                                         FStarC_Ident.range_of_lid
                                                           ed.FStarC_Syntax_Syntax.mname in
                                                       FStarC_Syntax_Syntax.mk
                                                         uu___17 uu___18 in
                                                     let f_b =
                                                       FStarC_Syntax_Syntax.null_binder
                                                         repr_t_applied in
                                                     let uu___17 =
                                                       let uu___18 =
                                                         let uu___19 =
                                                           FStarC_Syntax_Syntax.bv_to_name
                                                             f_b.FStarC_Syntax_Syntax.binder_bv in
                                                         FStarC_Syntax_Util.abs
                                                           (FStarC_Compiler_List.op_At
                                                              bs1 [f_b])
                                                           uu___19
                                                           FStar_Pervasives_Native.None in
                                                       let uu___19 =
                                                         FStarC_Ident.range_of_lid
                                                           ed.FStarC_Syntax_Syntax.mname in
                                                       {
                                                         FStarC_Syntax_Syntax.n
                                                           =
                                                           (uu___18.FStarC_Syntax_Syntax.n);
                                                         FStarC_Syntax_Syntax.pos
                                                           = uu___19;
                                                         FStarC_Syntax_Syntax.vars
                                                           =
                                                           (uu___18.FStarC_Syntax_Syntax.vars);
                                                         FStarC_Syntax_Syntax.hash_code
                                                           =
                                                           (uu___18.FStarC_Syntax_Syntax.hash_code)
                                                       } in
                                                     ([], uu___17)
                                                 | uu___16 ->
                                                     failwith "Impossible!"))
                                       | uu___13 -> ts in
                                     let r =
                                       (FStar_Pervasives_Native.snd
                                          stronger_repr).FStarC_Syntax_Syntax.pos in
                                     let uu___12 =
                                       check_and_gen1 "stronger_repr"
                                         Prims.int_one stronger_repr in
                                     match uu___12 with
                                     | (stronger_us, stronger_t, stronger_ty)
                                         ->
                                         ((let uu___14 =
                                             FStarC_Compiler_Effect.op_Bang
                                               dbg_LayeredEffectsTc in
                                           if uu___14
                                           then
                                             let uu___15 =
                                               FStarC_Syntax_Print.tscheme_to_string
                                                 (stronger_us, stronger_t) in
                                             let uu___16 =
                                               FStarC_Syntax_Print.tscheme_to_string
                                                 (stronger_us, stronger_ty) in
                                             FStarC_Compiler_Util.print2
                                               "stronger combinator typechecked with term: %s and type: %s\n"
                                               uu___15 uu___16
                                           else ());
                                          (let uu___14 =
                                             FStarC_Syntax_Subst.open_univ_vars
                                               stronger_us stronger_ty in
                                           match uu___14 with
                                           | (us, ty) ->
                                               let env =
                                                 FStarC_TypeChecker_Env.push_univ_vars
                                                   env0 us in
                                               let uu___15 =
                                                 let sig_ts =
                                                   let uu___16 = signature in
                                                   match uu___16 with
                                                   | (us1, t, uu___17) ->
                                                       (us1, t) in
                                                 let repr_ts =
                                                   let uu___16 = repr in
                                                   match uu___16 with
                                                   | (us1, t, uu___17) ->
                                                       (us1, t) in
                                                 let uu___16 =
                                                   FStarC_Compiler_List.hd us in
                                                 validate_indexed_effect_subcomp_shape
                                                   env
                                                   ed.FStarC_Syntax_Syntax.mname
                                                   ed.FStarC_Syntax_Syntax.mname
                                                   sig_ts sig_ts
                                                   (FStar_Pervasives_Native.Some
                                                      repr_ts)
                                                   (FStar_Pervasives_Native.Some
                                                      repr_ts) uu___16 ty
                                                   num_effect_params r in
                                               (match uu___15 with
                                                | (k, kind) ->
                                                    let uu___16 =
                                                      let uu___17 =
                                                        FStarC_Syntax_Subst.close_univ_vars
                                                          stronger_us k in
                                                      (stronger_us,
                                                        stronger_t, uu___17) in
                                                    (uu___16, kind))))) in
                              match uu___10 with
                              | (stronger_repr, subcomp_kind) ->
                                  (log_combinator "stronger_repr"
                                     stronger_repr;
                                   (let uu___12 =
                                      FStarC_Errors.with_ctx
                                        "While checking the if_then_else combinator"
                                        (fun uu___13 ->
                                           let if_then_else_ts =
                                             let ts =
                                               let uu___14 =
                                                 let uu___15 =
                                                   FStarC_Syntax_Util.get_layered_if_then_else_combinator
                                                     ed in
                                                 FStarC_Compiler_Util.must
                                                   uu___15 in
                                               FStar_Pervasives_Native.fst
                                                 uu___14 in
                                             let uu___14 =
                                               let uu___15 =
                                                 FStarC_Syntax_Subst.compress
                                                   (FStar_Pervasives_Native.snd
                                                      ts) in
                                               uu___15.FStarC_Syntax_Syntax.n in
                                             match uu___14 with
                                             | FStarC_Syntax_Syntax.Tm_unknown
                                                 ->
                                                 let signature_ts =
                                                   let uu___15 = signature in
                                                   match uu___15 with
                                                   | (us, t, uu___16) ->
                                                       (us, t) in
                                                 let uu___15 =
                                                   FStarC_TypeChecker_Env.inst_tscheme_with
                                                     signature_ts
                                                     [FStarC_Syntax_Syntax.U_unknown] in
                                                 (match uu___15 with
                                                  | (uu___16, signature_t) ->
                                                      let uu___17 =
                                                        let uu___18 =
                                                          FStarC_Syntax_Subst.compress
                                                            signature_t in
                                                        uu___18.FStarC_Syntax_Syntax.n in
                                                      (match uu___17 with
                                                       | FStarC_Syntax_Syntax.Tm_arrow
                                                           {
                                                             FStarC_Syntax_Syntax.bs1
                                                               = bs;
                                                             FStarC_Syntax_Syntax.comp
                                                               = uu___18;_}
                                                           ->
                                                           let bs1 =
                                                             FStarC_Syntax_Subst.open_binders
                                                               bs in
                                                           let repr_t =
                                                             let repr_ts =
                                                               let uu___19 =
                                                                 repr in
                                                               match uu___19
                                                               with
                                                               | (us, t,
                                                                  uu___20) ->
                                                                   (us, t) in
                                                             let uu___19 =
                                                               FStarC_TypeChecker_Env.inst_tscheme_with
                                                                 repr_ts
                                                                 [FStarC_Syntax_Syntax.U_unknown] in
                                                             FStar_Pervasives_Native.snd
                                                               uu___19 in
                                                           let repr_t_applied
                                                             =
                                                             let uu___19 =
                                                               let uu___20 =
                                                                 let uu___21
                                                                   =
                                                                   let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun b ->
                                                                    b.FStarC_Syntax_Syntax.binder_bv)
                                                                    bs1 in
                                                                    FStarC_Compiler_List.map
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    uu___23 in
                                                                   FStarC_Compiler_List.map
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___22 in
                                                                 {
                                                                   FStarC_Syntax_Syntax.hd
                                                                    = repr_t;
                                                                   FStarC_Syntax_Syntax.args
                                                                    = uu___21
                                                                 } in
                                                               FStarC_Syntax_Syntax.Tm_app
                                                                 uu___20 in
                                                             let uu___20 =
                                                               FStarC_Ident.range_of_lid
                                                                 ed.FStarC_Syntax_Syntax.mname in
                                                             FStarC_Syntax_Syntax.mk
                                                               uu___19
                                                               uu___20 in
                                                           let f_b =
                                                             FStarC_Syntax_Syntax.null_binder
                                                               repr_t_applied in
                                                           let g_b =
                                                             FStarC_Syntax_Syntax.null_binder
                                                               repr_t_applied in
                                                           let b_b =
                                                             FStarC_Syntax_Syntax.null_binder
                                                               FStarC_Syntax_Util.t_bool in
                                                           let uu___19 =
                                                             let uu___20 =
                                                               FStarC_Syntax_Util.abs
                                                                 (FStarC_Compiler_List.op_At
                                                                    bs1
                                                                    [f_b;
                                                                    g_b;
                                                                    b_b])
                                                                 repr_t_applied
                                                                 FStar_Pervasives_Native.None in
                                                             let uu___21 =
                                                               FStarC_Ident.range_of_lid
                                                                 ed.FStarC_Syntax_Syntax.mname in
                                                             {
                                                               FStarC_Syntax_Syntax.n
                                                                 =
                                                                 (uu___20.FStarC_Syntax_Syntax.n);
                                                               FStarC_Syntax_Syntax.pos
                                                                 = uu___21;
                                                               FStarC_Syntax_Syntax.vars
                                                                 =
                                                                 (uu___20.FStarC_Syntax_Syntax.vars);
                                                               FStarC_Syntax_Syntax.hash_code
                                                                 =
                                                                 (uu___20.FStarC_Syntax_Syntax.hash_code)
                                                             } in
                                                           ([], uu___19)
                                                       | uu___18 ->
                                                           failwith
                                                             "Impossible!"))
                                             | uu___15 -> ts in
                                           let r =
                                             (FStar_Pervasives_Native.snd
                                                if_then_else_ts).FStarC_Syntax_Syntax.pos in
                                           let uu___14 =
                                             check_and_gen1 "if_then_else"
                                               Prims.int_one if_then_else_ts in
                                           match uu___14 with
                                           | (if_then_else_us,
                                              if_then_else_t,
                                              if_then_else_ty) ->
                                               let uu___15 =
                                                 FStarC_Syntax_Subst.open_univ_vars
                                                   if_then_else_us
                                                   if_then_else_t in
                                               (match uu___15 with
                                                | (us, t) ->
                                                    let uu___16 =
                                                      FStarC_Syntax_Subst.open_univ_vars
                                                        if_then_else_us
                                                        if_then_else_ty in
                                                    (match uu___16 with
                                                     | (uu___17, ty) ->
                                                         let env =
                                                           FStarC_TypeChecker_Env.push_univ_vars
                                                             env0 us in
                                                         let uu___18 =
                                                           let sig_ts =
                                                             let uu___19 =
                                                               signature in
                                                             match uu___19
                                                             with
                                                             | (us1, t1,
                                                                uu___20) ->
                                                                 (us1, t1) in
                                                           let repr_ts =
                                                             let uu___19 =
                                                               repr in
                                                             match uu___19
                                                             with
                                                             | (us1, t1,
                                                                uu___20) ->
                                                                 (us1, t1) in
                                                           let uu___19 =
                                                             FStarC_Compiler_List.hd
                                                               us in
                                                           validate_indexed_effect_ite_shape
                                                             env
                                                             ed.FStarC_Syntax_Syntax.mname
                                                             sig_ts repr_ts
                                                             uu___19 ty t
                                                             num_effect_params
                                                             r in
                                                         (match uu___18 with
                                                          | (k, kind) ->
                                                              let uu___19 =
                                                                let uu___20 =
                                                                  FStarC_Syntax_Subst.close_univ_vars
                                                                    if_then_else_us
                                                                    k in
                                                                (if_then_else_us,
                                                                  uu___20,
                                                                  if_then_else_ty) in
                                                              (uu___19, kind))))) in
                                    match uu___12 with
                                    | (if_then_else, ite_kind) ->
                                        (log_combinator "if_then_else"
                                           if_then_else;
                                         FStarC_Errors.with_ctx
                                           "While checking if-then-else soundness"
                                           (fun uu___14 ->
                                              let r =
                                                let uu___15 =
                                                  let uu___16 =
                                                    let uu___17 =
                                                      let uu___18 =
                                                        FStarC_Syntax_Util.get_layered_if_then_else_combinator
                                                          ed in
                                                      FStarC_Compiler_Util.must
                                                        uu___18 in
                                                    FStar_Pervasives_Native.fst
                                                      uu___17 in
                                                  FStar_Pervasives_Native.snd
                                                    uu___16 in
                                                uu___15.FStarC_Syntax_Syntax.pos in
                                              let uu___15 = if_then_else in
                                              match uu___15 with
                                              | (ite_us, ite_t, uu___16) ->
                                                  let uu___17 =
                                                    FStarC_Syntax_Subst.open_univ_vars
                                                      ite_us ite_t in
                                                  (match uu___17 with
                                                   | (us, ite_t1) ->
                                                       let uu___18 =
                                                         let uu___19 =
                                                           let uu___20 =
                                                             FStarC_Syntax_Subst.compress
                                                               ite_t1 in
                                                           uu___20.FStarC_Syntax_Syntax.n in
                                                         match uu___19 with
                                                         | FStarC_Syntax_Syntax.Tm_abs
                                                             {
                                                               FStarC_Syntax_Syntax.bs
                                                                 = bs;
                                                               FStarC_Syntax_Syntax.body
                                                                 = uu___20;
                                                               FStarC_Syntax_Syntax.rc_opt
                                                                 = uu___21;_}
                                                             ->
                                                             let bs1 =
                                                               FStarC_Syntax_Subst.open_binders
                                                                 bs in
                                                             let uu___22 =
                                                               let uu___23 =
                                                                 let uu___24
                                                                   =
                                                                   FStarC_Compiler_List.splitAt
                                                                    ((FStarC_Compiler_List.length
                                                                    bs1) -
                                                                    (Prims.of_int (3)))
                                                                    bs1 in
                                                                 FStar_Pervasives_Native.snd
                                                                   uu___24 in
                                                               let uu___24 =
                                                                 uu___23 in
                                                               match uu___24
                                                               with
                                                               | f::g::p::[]
                                                                   ->
                                                                   (f, g, p) in
                                                             (match uu___22
                                                              with
                                                              | (f_b, g_b,
                                                                 p_b) ->
                                                                  let env =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_Env.push_univ_vars
                                                                    env0 us in
                                                                    FStarC_TypeChecker_Env.push_binders
                                                                    uu___23
                                                                    bs1 in
                                                                  let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun b ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b.FStarC_Syntax_Syntax.binder_bv in
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Syntax_Util.aqual_of_binder
                                                                    b in
                                                                    (uu___26,
                                                                    uu___27))
                                                                    bs1 in
                                                                    FStarC_Syntax_Syntax.mk_Tm_app
                                                                    ite_t1
                                                                    uu___25 r in
                                                                    FStarC_TypeChecker_Normalize.normalize
                                                                    [FStarC_TypeChecker_Env.Beta]
                                                                    env
                                                                    uu___24 in
                                                                  let uu___24
                                                                    =
                                                                    FStarC_Compiler_List.hd
                                                                    bs1 in
                                                                  let uu___25
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    p_b.FStarC_Syntax_Syntax.binder_bv in
                                                                  (env,
                                                                    uu___23,
                                                                    uu___24,
                                                                    f_b, g_b,
                                                                    uu___25))
                                                         | uu___20 ->
                                                             failwith
                                                               "Impossible! ite_t must have been an abstraction with at least 3 binders" in
                                                       (match uu___18 with
                                                        | (env,
                                                           ite_t_applied,
                                                           a_b, f_b, g_b,
                                                           p_t) ->
                                                            let uu___19 =
                                                              let uu___20 =
                                                                stronger_repr in
                                                              match uu___20
                                                              with
                                                              | (uu___21,
                                                                 uu___22,
                                                                 subcomp_ty)
                                                                  ->
                                                                  let uu___23
                                                                    =
                                                                    FStarC_Syntax_Subst.open_univ_vars
                                                                    us
                                                                    subcomp_ty in
                                                                  (match uu___23
                                                                   with
                                                                   | 
                                                                   (uu___24,
                                                                    subcomp_ty1)
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    subcomp_ty1 in
                                                                    uu___26.FStarC_Syntax_Syntax.n in
                                                                    (match uu___25
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_arrow
                                                                    {
                                                                    FStarC_Syntax_Syntax.bs1
                                                                    = bs;
                                                                    FStarC_Syntax_Syntax.comp
                                                                    = c;_} ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Syntax_Subst.open_comp
                                                                    bs c in
                                                                    (match uu___26
                                                                    with
                                                                    | 
                                                                    (bs1, c1)
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStarC_Compiler_List.hd
                                                                    bs1 in
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Compiler_List.tl
                                                                    bs1 in
                                                                    (uu___28,
                                                                    uu___29) in
                                                                    (match uu___27
                                                                    with
                                                                    | 
                                                                    (a_b1,
                                                                    rest_bs)
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Compiler_List.splitAt
                                                                    ((FStarC_Compiler_List.length
                                                                    rest_bs)
                                                                    -
                                                                    Prims.int_one)
                                                                    rest_bs in
                                                                    match uu___29
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_Compiler_List.hd
                                                                    l2 in
                                                                    (l1,
                                                                    uu___30) in
                                                                    (match uu___28
                                                                    with
                                                                    | 
                                                                    (rest_bs1,
                                                                    f_b1) ->
                                                                    (a_b1,
                                                                    rest_bs1,
                                                                    f_b1, c1))))
                                                                    | 
                                                                    uu___26
                                                                    ->
                                                                    failwith
                                                                    "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")) in
                                                            (match uu___19
                                                             with
                                                             | (subcomp_a_b,
                                                                subcomp_bs,
                                                                subcomp_f_b,
                                                                subcomp_c) ->
                                                                 let check_branch
                                                                   env1
                                                                   ite_f_or_g_sort
                                                                   attr_opt =
                                                                   let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    ((subcomp_a_b.FStarC_Syntax_Syntax.binder_bv),
                                                                    uu___25) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___24 in
                                                                    [uu___23] in
                                                                    (uu___22,
                                                                    [],
                                                                    FStarC_TypeChecker_Env.trivial_guard) in
                                                                    FStarC_Compiler_List.fold_left
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    fun b ->
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    (subst,
                                                                    uvars, g)
                                                                    ->
                                                                    let sort
                                                                    =
                                                                    FStarC_Syntax_Subst.subst
                                                                    subst
                                                                    (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                                    let uu___23
                                                                    =
                                                                    let ctx_uvar_meta
                                                                    =
                                                                    FStarC_Compiler_Util.map_option
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStarC_Syntax_Syntax.Ctx_uvar_meta_attr
                                                                    uu___24)
                                                                    attr_opt in
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_binder
                                                                    b in
                                                                    FStarC_Compiler_Util.format1
                                                                    "uvar for subcomp %s binder when checking ite soundness"
                                                                    uu___25 in
                                                                    FStarC_TypeChecker_Env.new_implicit_var_aux
                                                                    uu___24 r
                                                                    env1 sort
                                                                    FStarC_Syntax_Syntax.Strict
                                                                    ctx_uvar_meta
                                                                    false in
                                                                    (match uu___23
                                                                    with
                                                                    | 
                                                                    (t,
                                                                    uu___24,
                                                                    g_t) ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_Common.conj_guard
                                                                    g g_t in
                                                                    ((FStarC_Compiler_List.op_At
                                                                    subst
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    ((b.FStarC_Syntax_Syntax.binder_bv),
                                                                    t)]),
                                                                    (FStarC_Compiler_List.op_At
                                                                    uvars 
                                                                    [t]),
                                                                    uu___25)))
                                                                    uu___21
                                                                    subcomp_bs in
                                                                   match uu___20
                                                                   with
                                                                   | 
                                                                   (subst,
                                                                    uvars,
                                                                    g_uvars)
                                                                    ->
                                                                    let subcomp_f_sort
                                                                    =
                                                                    FStarC_Syntax_Subst.subst
                                                                    subst
                                                                    (subcomp_f_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                                    let c =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Syntax_Subst.subst_comp
                                                                    subst
                                                                    subcomp_c in
                                                                    FStarC_TypeChecker_Env.unfold_effect_abbrev
                                                                    env1
                                                                    uu___21 in
                                                                    let g_f_or_g
                                                                    =
                                                                    FStarC_TypeChecker_Rel.layered_effect_teq
                                                                    env1
                                                                    subcomp_f_sort
                                                                    ite_f_or_g_sort
                                                                    FStar_Pervasives_Native.None in
                                                                    let g_c =
                                                                    FStarC_TypeChecker_Rel.layered_effect_teq
                                                                    env1
                                                                    c.FStarC_Syntax_Syntax.result_typ
                                                                    ite_t_applied
                                                                    FStar_Pervasives_Native.None in
                                                                    let fml =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Compiler_List.hd
                                                                    c.FStarC_Syntax_Syntax.comp_univs in
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Compiler_List.hd
                                                                    c.FStarC_Syntax_Syntax.effect_args in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___23 in
                                                                    FStarC_TypeChecker_Env.pure_precondition_for_trivial_post
                                                                    env1
                                                                    uu___21
                                                                    c.FStarC_Syntax_Syntax.result_typ
                                                                    uu___22 r in
                                                                    let g_precondition
                                                                    =
                                                                    match attr_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStarC_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStarC_TypeChecker_Common.NonTrivial
                                                                    fml)
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    attr ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Syntax_Util.mk_squash
                                                                    FStarC_Syntax_Syntax.U_zero
                                                                    fml in
                                                                    FStarC_TypeChecker_Env.new_implicit_var_aux
                                                                    "tc_layered_effect_decl.g_precondition"
                                                                    r env1
                                                                    uu___22
                                                                    FStarC_Syntax_Syntax.Strict
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStarC_Syntax_Syntax.Ctx_uvar_meta_attr
                                                                    attr))
                                                                    false in
                                                                    (match uu___21
                                                                    with
                                                                    | 
                                                                    (uu___22,
                                                                    uu___23,
                                                                    g) -> g) in
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_Env.conj_guards
                                                                    [g_uvars;
                                                                    g_f_or_g;
                                                                    g_c;
                                                                    g_precondition] in
                                                                    FStarC_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu___21 in
                                                                 let ite_soundness_tac_attr
                                                                   =
                                                                   let uu___20
                                                                    =
                                                                    FStarC_Syntax_Util.get_attribute
                                                                    FStarC_Parser_Const.ite_soundness_by_attr
                                                                    attrs in
                                                                   match uu___20
                                                                   with
                                                                   | 
                                                                   FStar_Pervasives_Native.Some
                                                                    ((t,
                                                                    uu___21)::uu___22)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    t
                                                                   | 
                                                                   uu___21 ->
                                                                    FStar_Pervasives_Native.None in
                                                                 ((let env1 =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Syntax_Util.b2t
                                                                    p_t in
                                                                    FStarC_Syntax_Util.mk_squash
                                                                    FStarC_Syntax_Syntax.U_zero
                                                                    uu___22 in
                                                                    FStarC_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    uu___21 in
                                                                    FStarC_TypeChecker_Env.push_bv
                                                                    env
                                                                    uu___20 in
                                                                   check_branch
                                                                    env1
                                                                    (f_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                                                    ite_soundness_tac_attr);
                                                                  (let not_p
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Syntax_Syntax.lid_as_fv
                                                                    FStarC_Parser_Const.not_lid
                                                                    FStar_Pervasives_Native.None in
                                                                    FStarC_Syntax_Syntax.fv_to_tm
                                                                    uu___21 in
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Syntax_Util.b2t
                                                                    p_t in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___23 in
                                                                    [uu___22] in
                                                                    FStarC_Syntax_Syntax.mk_Tm_app
                                                                    uu___20
                                                                    uu___21 r in
                                                                   let env1 =
                                                                    let uu___20
                                                                    =
                                                                    FStarC_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    not_p in
                                                                    FStarC_TypeChecker_Env.push_bv
                                                                    env
                                                                    uu___20 in
                                                                   check_branch
                                                                    env1
                                                                    (g_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                                                    ite_soundness_tac_attr))))));
                                         (let close_ =
                                            FStarC_Errors.with_ctx
                                              "While checking the close combinator"
                                              (fun uu___14 ->
                                                 let ts_opt =
                                                   FStarC_Syntax_Util.get_layered_close_combinator
                                                     ed in
                                                 match ts_opt with
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     FStar_Pervasives_Native.None
                                                 | FStar_Pervasives_Native.Some
                                                     close_ts ->
                                                     let r =
                                                       (FStar_Pervasives_Native.snd
                                                          close_ts).FStarC_Syntax_Syntax.pos in
                                                     let uu___15 =
                                                       check_and_gen1 "close"
                                                         (Prims.of_int (2))
                                                         close_ts in
                                                     (match uu___15 with
                                                      | (close_us, close_t,
                                                         close_ty) ->
                                                          let uu___16 =
                                                            FStarC_Syntax_Subst.open_univ_vars
                                                              close_us
                                                              close_t in
                                                          (match uu___16 with
                                                           | (us, t) ->
                                                               let env =
                                                                 FStarC_TypeChecker_Env.push_univ_vars
                                                                   env0 us in
                                                               let k =
                                                                 let sig_ts =
                                                                   let uu___17
                                                                    =
                                                                    signature in
                                                                   match uu___17
                                                                   with
                                                                   | 
                                                                   (us1, t1,
                                                                    uu___18)
                                                                    ->
                                                                    (us1, t1) in
                                                                 let repr_ts
                                                                   =
                                                                   let uu___17
                                                                    = repr in
                                                                   match uu___17
                                                                   with
                                                                   | 
                                                                   (us1, t1,
                                                                    uu___18)
                                                                    ->
                                                                    (us1, t1) in
                                                                 let uu___17
                                                                   = us in
                                                                 match uu___17
                                                                 with
                                                                 | u_a::u_b::[]
                                                                    ->
                                                                    validate_indexed_effect_close_shape
                                                                    env
                                                                    ed.FStarC_Syntax_Syntax.mname
                                                                    sig_ts
                                                                    repr_ts
                                                                    u_a u_b t
                                                                    num_effect_params
                                                                    r in
                                                               let uu___17 =
                                                                 let uu___18
                                                                   =
                                                                   FStarC_Syntax_Subst.close_univ_vars
                                                                    close_us
                                                                    k in
                                                                 (close_us,
                                                                   uu___18,
                                                                   close_ty) in
                                                               FStar_Pervasives_Native.Some
                                                                 uu___17))) in
                                          FStarC_Errors.with_ctx
                                            "While checking the soundness of the close combinator"
                                            (fun uu___14 ->
                                               match close_ with
                                               | FStar_Pervasives_Native.None
                                                   -> ()
                                               | FStar_Pervasives_Native.Some
                                                   close_1 ->
                                                   let uu___15 = close_1 in
                                                   (match uu___15 with
                                                    | (us, close_tm, uu___16)
                                                        ->
                                                        let r =
                                                          close_tm.FStarC_Syntax_Syntax.pos in
                                                        ((let supported_subcomp
                                                            =
                                                            match subcomp_kind
                                                            with
                                                            | FStarC_Syntax_Syntax.Substitutive_combinator
                                                                l ->
                                                                Prims.op_Negation
                                                                  (FStarC_Compiler_List.contains
                                                                    FStarC_Syntax_Syntax.Ad_hoc_binder
                                                                    l)
                                                            | uu___18 ->
                                                                false in
                                                          if
                                                            Prims.op_Negation
                                                              supported_subcomp
                                                          then
                                                            FStarC_Errors.raise_error
                                                              FStarC_Class_HasRange.hasRange_range
                                                              r
                                                              FStarC_Errors_Codes.Fatal_UnexpectedEffect
                                                              ()
                                                              (Obj.magic
                                                                 FStarC_Errors_Msg.is_error_message_string)
                                                              (Obj.magic
                                                                 "close combinator is only allowed for effects with substitutive subcomp")
                                                          else ());
                                                         (let uu___18 =
                                                            FStarC_Syntax_Subst.open_univ_vars
                                                              us close_tm in
                                                          match uu___18 with
                                                          | (us1, close_tm1)
                                                              ->
                                                              let uu___19 =
                                                                FStarC_Syntax_Util.abs_formals
                                                                  close_tm1 in
                                                              (match uu___19
                                                               with
                                                               | (close_bs,
                                                                  close_body,
                                                                  uu___20) ->
                                                                   let uu___21
                                                                    =
                                                                    close_bs in
                                                                   (match uu___21
                                                                    with
                                                                    | 
                                                                    a_b::b_b::close_bs1
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Compiler_List.splitAt
                                                                    ((FStarC_Compiler_List.length
                                                                    close_bs1)
                                                                    -
                                                                    Prims.int_one)
                                                                    close_bs1 in
                                                                    (match uu___22
                                                                    with
                                                                    | 
                                                                    (is_bs,
                                                                    uu___23)
                                                                    ->
                                                                    let x_bv
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    FStarC_Syntax_Syntax.gen_bv
                                                                    "x"
                                                                    FStar_Pervasives_Native.None
                                                                    uu___24 in
                                                                    let args1
                                                                    =
                                                                    FStarC_Compiler_List.map
                                                                    (fun i_b
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    i_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    x_bv in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___27 in
                                                                    [uu___26] in
                                                                    FStarC_Syntax_Syntax.mk_Tm_app
                                                                    uu___24
                                                                    uu___25 r)
                                                                    is_bs in
                                                                    let args2
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    close_body in
                                                                    uu___25.FStarC_Syntax_Syntax.n in
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_app
                                                                    {
                                                                    FStarC_Syntax_Syntax.hd
                                                                    = uu___25;
                                                                    FStarC_Syntax_Syntax.args
                                                                    = a::args;_}
                                                                    ->
                                                                    FStarC_Compiler_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    args
                                                                    | 
                                                                    uu___25
                                                                    ->
                                                                    FStarC_Errors.raise_error
                                                                    FStarC_Class_HasRange.hasRange_range
                                                                    r
                                                                    FStarC_Errors_Codes.Fatal_UnexpectedEffect
                                                                    ()
                                                                    (Obj.magic
                                                                    FStarC_Errors_Msg.is_error_message_string)
                                                                    (Obj.magic
                                                                    "close combinator body not a repr") in
                                                                    let env =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_binder
                                                                    x_bv in
                                                                    [uu___26] in
                                                                    FStarC_Compiler_List.op_At
                                                                    (a_b ::
                                                                    b_b ::
                                                                    is_bs)
                                                                    uu___25 in
                                                                    FStarC_TypeChecker_Env.push_binders
                                                                    env0
                                                                    uu___24 in
                                                                    let subcomp_ts
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    stronger_repr in
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    (us2,
                                                                    uu___25,
                                                                    t) ->
                                                                    (us2, t) in
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Compiler_List.hd
                                                                    us1 in
                                                                    FStarC_Syntax_Syntax.U_name
                                                                    uu___27 in
                                                                    [uu___26] in
                                                                    FStarC_TypeChecker_Env.inst_tscheme_with
                                                                    subcomp_ts
                                                                    uu___25 in
                                                                    (match uu___24
                                                                    with
                                                                    | 
                                                                    (uu___25,
                                                                    subcomp_t)
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Syntax_Util.arrow_formals_comp
                                                                    subcomp_t in
                                                                    (match uu___26
                                                                    with
                                                                    | 
                                                                    (a_b_subcomp::subcomp_bs,
                                                                    subcomp_c)
                                                                    ->
                                                                    let subcomp_substs
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    a_b.FStarC_Syntax_Syntax.binder_bv in
                                                                    ((a_b_subcomp.FStarC_Syntax_Syntax.binder_bv),
                                                                    uu___29) in
                                                                    FStarC_Syntax_Syntax.NT
                                                                    uu___28 in
                                                                    [uu___27] in
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Compiler_List.splitAt
                                                                    (FStarC_Compiler_List.length
                                                                    args1)
                                                                    subcomp_bs in
                                                                    (match uu___27
                                                                    with
                                                                    | 
                                                                    (subcomp_f_bs,
                                                                    subcomp_bs1)
                                                                    ->
                                                                    let subcomp_substs1
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStarC_Compiler_List.map2
                                                                    (fun b ->
                                                                    fun arg1
                                                                    ->
                                                                    FStarC_Syntax_Syntax.NT
                                                                    ((b.FStarC_Syntax_Syntax.binder_bv),
                                                                    arg1))
                                                                    subcomp_f_bs
                                                                    args1 in
                                                                    FStarC_Compiler_List.op_At
                                                                    subcomp_substs
                                                                    uu___28 in
                                                                    let uu___28
                                                                    =
                                                                    FStarC_Compiler_List.splitAt
                                                                    (FStarC_Compiler_List.length
                                                                    args2)
                                                                    subcomp_bs1 in
                                                                    (match uu___28
                                                                    with
                                                                    | 
                                                                    (subcomp_g_bs,
                                                                    uu___29)
                                                                    ->
                                                                    let subcomp_substs2
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStarC_Compiler_List.map2
                                                                    (fun b ->
                                                                    fun arg2
                                                                    ->
                                                                    FStarC_Syntax_Syntax.NT
                                                                    ((b.FStarC_Syntax_Syntax.binder_bv),
                                                                    arg2))
                                                                    subcomp_g_bs
                                                                    args2 in
                                                                    FStarC_Compiler_List.op_At
                                                                    subcomp_substs1
                                                                    uu___30 in
                                                                    let subcomp_c1
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStarC_Syntax_Subst.subst_comp
                                                                    subcomp_substs2
                                                                    subcomp_c in
                                                                    FStarC_TypeChecker_Env.unfold_effect_abbrev
                                                                    env
                                                                    uu___30 in
                                                                    let fml =
                                                                    let uu___30
                                                                    =
                                                                    FStarC_Compiler_List.hd
                                                                    subcomp_c1.FStarC_Syntax_Syntax.comp_univs in
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    FStarC_Compiler_List.hd
                                                                    subcomp_c1.FStarC_Syntax_Syntax.effect_args in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___32 in
                                                                    FStarC_TypeChecker_Env.pure_precondition_for_trivial_post
                                                                    env
                                                                    uu___30
                                                                    subcomp_c1.FStarC_Syntax_Syntax.result_typ
                                                                    uu___31 r in
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStarC_TypeChecker_Common.NonTrivial
                                                                    fml) in
                                                                    FStarC_TypeChecker_Rel.force_trivial_guard
                                                                    env
                                                                    uu___30)))))))))));
                                          (let tc_action env act =
                                             let env01 = env in
                                             let r =
                                               (act.FStarC_Syntax_Syntax.action_defn).FStarC_Syntax_Syntax.pos in
                                             if
                                               (FStarC_Compiler_List.length
                                                  act.FStarC_Syntax_Syntax.action_params)
                                                 <> Prims.int_zero
                                             then
                                               (let uu___15 =
                                                  let uu___16 =
                                                    FStarC_Ident.string_of_lid
                                                      ed.FStarC_Syntax_Syntax.mname in
                                                  let uu___17 =
                                                    FStarC_Ident.string_of_lid
                                                      act.FStarC_Syntax_Syntax.action_name in
                                                  let uu___18 =
                                                    FStarC_Class_Show.show
                                                      (FStarC_Class_Show.show_list
                                                         FStarC_Syntax_Print.showable_binder)
                                                      act.FStarC_Syntax_Syntax.action_params in
                                                  FStarC_Compiler_Util.format3
                                                    "Action %s:%s has non-empty action params (%s)"
                                                    uu___16 uu___17 uu___18 in
                                                FStarC_Errors.raise_error
                                                  FStarC_Class_HasRange.hasRange_range
                                                  r
                                                  FStarC_Errors_Codes.Fatal_MalformedActionDeclaration
                                                  ()
                                                  (Obj.magic
                                                     FStarC_Errors_Msg.is_error_message_string)
                                                  (Obj.magic uu___15))
                                             else ();
                                             (let uu___15 =
                                                let uu___16 =
                                                  FStarC_Syntax_Subst.univ_var_opening
                                                    act.FStarC_Syntax_Syntax.action_univs in
                                                match uu___16 with
                                                | (usubst, us) ->
                                                    let uu___17 =
                                                      FStarC_TypeChecker_Env.push_univ_vars
                                                        env us in
                                                    let uu___18 =
                                                      let uu___19 =
                                                        FStarC_Syntax_Subst.subst
                                                          usubst
                                                          act.FStarC_Syntax_Syntax.action_defn in
                                                      let uu___20 =
                                                        FStarC_Syntax_Subst.subst
                                                          usubst
                                                          act.FStarC_Syntax_Syntax.action_typ in
                                                      {
                                                        FStarC_Syntax_Syntax.action_name
                                                          =
                                                          (act.FStarC_Syntax_Syntax.action_name);
                                                        FStarC_Syntax_Syntax.action_unqualified_name
                                                          =
                                                          (act.FStarC_Syntax_Syntax.action_unqualified_name);
                                                        FStarC_Syntax_Syntax.action_univs
                                                          = us;
                                                        FStarC_Syntax_Syntax.action_params
                                                          =
                                                          (act.FStarC_Syntax_Syntax.action_params);
                                                        FStarC_Syntax_Syntax.action_defn
                                                          = uu___19;
                                                        FStarC_Syntax_Syntax.action_typ
                                                          = uu___20
                                                      } in
                                                    (uu___17, uu___18) in
                                              match uu___15 with
                                              | (env1, act1) ->
                                                  let act_typ =
                                                    let uu___16 =
                                                      let uu___17 =
                                                        FStarC_Syntax_Subst.compress
                                                          act1.FStarC_Syntax_Syntax.action_typ in
                                                      uu___17.FStarC_Syntax_Syntax.n in
                                                    match uu___16 with
                                                    | FStarC_Syntax_Syntax.Tm_arrow
                                                        {
                                                          FStarC_Syntax_Syntax.bs1
                                                            = bs;
                                                          FStarC_Syntax_Syntax.comp
                                                            = c;_}
                                                        ->
                                                        let ct =
                                                          FStarC_TypeChecker_Env.comp_to_comp_typ
                                                            env1 c in
                                                        let uu___17 =
                                                          FStarC_Ident.lid_equals
                                                            ct.FStarC_Syntax_Syntax.effect_name
                                                            ed.FStarC_Syntax_Syntax.mname in
                                                        if uu___17
                                                        then
                                                          let repr_ts =
                                                            let uu___18 =
                                                              repr in
                                                            match uu___18
                                                            with
                                                            | (us, t,
                                                               uu___19) ->
                                                                (us, t) in
                                                          let repr1 =
                                                            let uu___18 =
                                                              FStarC_TypeChecker_Env.inst_tscheme_with
                                                                repr_ts
                                                                ct.FStarC_Syntax_Syntax.comp_univs in
                                                            FStar_Pervasives_Native.snd
                                                              uu___18 in
                                                          let repr2 =
                                                            let uu___18 =
                                                              let uu___19 =
                                                                FStarC_Syntax_Syntax.as_arg
                                                                  ct.FStarC_Syntax_Syntax.result_typ in
                                                              uu___19 ::
                                                                (ct.FStarC_Syntax_Syntax.effect_args) in
                                                            FStarC_Syntax_Syntax.mk_Tm_app
                                                              repr1 uu___18 r in
                                                          let c1 =
                                                            FStarC_Syntax_Syntax.mk_Total
                                                              repr2 in
                                                          FStarC_Syntax_Util.arrow
                                                            bs c1
                                                        else
                                                          act1.FStarC_Syntax_Syntax.action_typ
                                                    | uu___17 ->
                                                        act1.FStarC_Syntax_Syntax.action_typ in
                                                  let uu___16 =
                                                    FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                      env1 act_typ in
                                                  (match uu___16 with
                                                   | (act_typ1, uu___17, g_t)
                                                       ->
                                                       let uu___18 =
                                                         let uu___19 =
                                                           let uu___20 =
                                                             FStarC_TypeChecker_Env.set_expected_typ
                                                               env1 act_typ1 in
                                                           {
                                                             FStarC_TypeChecker_Env.solver
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.solver);
                                                             FStarC_TypeChecker_Env.range
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.range);
                                                             FStarC_TypeChecker_Env.curmodule
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.curmodule);
                                                             FStarC_TypeChecker_Env.gamma
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.gamma);
                                                             FStarC_TypeChecker_Env.gamma_sig
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.gamma_sig);
                                                             FStarC_TypeChecker_Env.gamma_cache
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.gamma_cache);
                                                             FStarC_TypeChecker_Env.modules
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.modules);
                                                             FStarC_TypeChecker_Env.expected_typ
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.expected_typ);
                                                             FStarC_TypeChecker_Env.sigtab
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.sigtab);
                                                             FStarC_TypeChecker_Env.attrtab
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.attrtab);
                                                             FStarC_TypeChecker_Env.instantiate_imp
                                                               = false;
                                                             FStarC_TypeChecker_Env.effects
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.effects);
                                                             FStarC_TypeChecker_Env.generalize
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.generalize);
                                                             FStarC_TypeChecker_Env.letrecs
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.letrecs);
                                                             FStarC_TypeChecker_Env.top_level
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.top_level);
                                                             FStarC_TypeChecker_Env.check_uvars
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.check_uvars);
                                                             FStarC_TypeChecker_Env.use_eq_strict
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.use_eq_strict);
                                                             FStarC_TypeChecker_Env.is_iface
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.is_iface);
                                                             FStarC_TypeChecker_Env.admit
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.admit);
                                                             FStarC_TypeChecker_Env.lax_universes
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.lax_universes);
                                                             FStarC_TypeChecker_Env.phase1
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.phase1);
                                                             FStarC_TypeChecker_Env.failhard
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.failhard);
                                                             FStarC_TypeChecker_Env.flychecking
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.flychecking);
                                                             FStarC_TypeChecker_Env.uvar_subtyping
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.uvar_subtyping);
                                                             FStarC_TypeChecker_Env.intactics
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.intactics);
                                                             FStarC_TypeChecker_Env.nocoerce
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.nocoerce);
                                                             FStarC_TypeChecker_Env.tc_term
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.tc_term);
                                                             FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                                             FStarC_TypeChecker_Env.universe_of
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.universe_of);
                                                             FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                                             FStarC_TypeChecker_Env.teq_nosmt_force
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.teq_nosmt_force);
                                                             FStarC_TypeChecker_Env.subtype_nosmt_force
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                                             FStarC_TypeChecker_Env.qtbl_name_and_index
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                                             FStarC_TypeChecker_Env.normalized_eff_names
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.normalized_eff_names);
                                                             FStarC_TypeChecker_Env.fv_delta_depths
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.fv_delta_depths);
                                                             FStarC_TypeChecker_Env.proof_ns
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.proof_ns);
                                                             FStarC_TypeChecker_Env.synth_hook
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.synth_hook);
                                                             FStarC_TypeChecker_Env.try_solve_implicits_hook
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                                             FStarC_TypeChecker_Env.splice
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.splice);
                                                             FStarC_TypeChecker_Env.mpreprocess
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.mpreprocess);
                                                             FStarC_TypeChecker_Env.postprocess
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.postprocess);
                                                             FStarC_TypeChecker_Env.identifier_info
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.identifier_info);
                                                             FStarC_TypeChecker_Env.tc_hooks
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.tc_hooks);
                                                             FStarC_TypeChecker_Env.dsenv
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.dsenv);
                                                             FStarC_TypeChecker_Env.nbe
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.nbe);
                                                             FStarC_TypeChecker_Env.strict_args_tab
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.strict_args_tab);
                                                             FStarC_TypeChecker_Env.erasable_types_tab
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.erasable_types_tab);
                                                             FStarC_TypeChecker_Env.enable_defer_to_tac
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                                             FStarC_TypeChecker_Env.unif_allow_ref_guards
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                                             FStarC_TypeChecker_Env.erase_erasable_args
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.erase_erasable_args);
                                                             FStarC_TypeChecker_Env.core_check
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.core_check);
                                                             FStarC_TypeChecker_Env.missing_decl
                                                               =
                                                               (uu___20.FStarC_TypeChecker_Env.missing_decl)
                                                           } in
                                                         FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                           uu___19
                                                           act1.FStarC_Syntax_Syntax.action_defn in
                                                       (match uu___18 with
                                                        | (act_defn, uu___19,
                                                           g_d) ->
                                                            ((let uu___21 =
                                                                (FStarC_Compiler_Debug.medium
                                                                   ())
                                                                  ||
                                                                  (FStarC_Compiler_Effect.op_Bang
                                                                    dbg_LayeredEffectsTc) in
                                                              if uu___21
                                                              then
                                                                let uu___22 =
                                                                  FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    act_defn in
                                                                let uu___23 =
                                                                  FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    act_typ1 in
                                                                FStarC_Compiler_Util.print2
                                                                  "Typechecked action definition: %s and action type: %s\n"
                                                                  uu___22
                                                                  uu___23
                                                              else ());
                                                             (let uu___21 =
                                                                let act_typ2
                                                                  =
                                                                  FStarC_TypeChecker_Normalize.normalize
                                                                    [FStarC_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ1 in
                                                                let uu___22 =
                                                                  let uu___23
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    act_typ2 in
                                                                  uu___23.FStarC_Syntax_Syntax.n in
                                                                match uu___22
                                                                with
                                                                | FStarC_Syntax_Syntax.Tm_arrow
                                                                    {
                                                                    FStarC_Syntax_Syntax.bs1
                                                                    = bs;
                                                                    FStarC_Syntax_Syntax.comp
                                                                    = uu___23;_}
                                                                    ->
                                                                    let bs1 =
                                                                    FStarC_Syntax_Subst.open_binders
                                                                    bs in
                                                                    let env2
                                                                    =
                                                                    FStarC_TypeChecker_Env.push_binders
                                                                    env1 bs1 in
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Syntax_Util.type_u
                                                                    () in
                                                                    (match uu___24
                                                                    with
                                                                    | 
                                                                    (t, u) ->
                                                                    let reason
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_Ident.string_of_lid
                                                                    ed.FStarC_Syntax_Syntax.mname in
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Ident.string_of_lid
                                                                    act1.FStarC_Syntax_Syntax.action_name in
                                                                    FStarC_Compiler_Util.format2
                                                                    "implicit for return type of action %s:%s"
                                                                    uu___25
                                                                    uu___26 in
                                                                    let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_Util.new_implicit_var
                                                                    reason r
                                                                    env2 t
                                                                    false in
                                                                    (match uu___25
                                                                    with
                                                                    | 
                                                                    (a_tm,
                                                                    uu___26,
                                                                    g_tm) ->
                                                                    let uu___27
                                                                    =
                                                                    fresh_repr
                                                                    r env2 u
                                                                    a_tm in
                                                                    (match uu___27
                                                                    with
                                                                    | 
                                                                    (repr1,
                                                                    g) ->
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_Total
                                                                    repr1 in
                                                                    FStarC_Syntax_Util.arrow
                                                                    bs1
                                                                    uu___29 in
                                                                    let uu___29
                                                                    =
                                                                    FStarC_TypeChecker_Env.conj_guard
                                                                    g g_tm in
                                                                    (uu___28,
                                                                    uu___29))))
                                                                | uu___23 ->
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Ident.showable_lident
                                                                    ed.FStarC_Syntax_Syntax.mname in
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Ident.showable_lident
                                                                    act1.FStarC_Syntax_Syntax.action_name in
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    act_typ2 in
                                                                    FStarC_Compiler_Util.format3
                                                                    "Unexpected non-function type for action %s:%s (%s)"
                                                                    uu___25
                                                                    uu___26
                                                                    uu___27 in
                                                                    FStarC_Errors.raise_error
                                                                    FStarC_Class_HasRange.hasRange_range
                                                                    r
                                                                    FStarC_Errors_Codes.Fatal_ActionMustHaveFunctionType
                                                                    ()
                                                                    (Obj.magic
                                                                    FStarC_Errors_Msg.is_error_message_string)
                                                                    (Obj.magic
                                                                    uu___24) in
                                                              match uu___21
                                                              with
                                                              | (k, g_k) ->
                                                                  ((let uu___23
                                                                    =
                                                                    (FStarC_Compiler_Debug.medium
                                                                    ()) ||
                                                                    (FStarC_Compiler_Effect.op_Bang
                                                                    dbg_LayeredEffectsTc) in
                                                                    if
                                                                    uu___23
                                                                    then
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    k in
                                                                    FStarC_Compiler_Util.print1
                                                                    "Expected action type: %s\n"
                                                                    uu___24
                                                                    else ());
                                                                   (let g =
                                                                    FStarC_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ1
                                                                    k in
                                                                    FStarC_Compiler_List.iter
                                                                    (FStarC_TypeChecker_Rel.force_trivial_guard
                                                                    env1)
                                                                    [g_t;
                                                                    g_d;
                                                                    g_k;
                                                                    g];
                                                                    (
                                                                    let uu___25
                                                                    =
                                                                    (FStarC_Compiler_Debug.medium
                                                                    ()) ||
                                                                    (FStarC_Compiler_Effect.op_Bang
                                                                    dbg_LayeredEffectsTc) in
                                                                    if
                                                                    uu___25
                                                                    then
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    k in
                                                                    FStarC_Compiler_Util.print1
                                                                    "Expected action type after unification: %s\n"
                                                                    uu___26
                                                                    else ());
                                                                    (
                                                                    let act_typ2
                                                                    =
                                                                    let err_msg
                                                                    t =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_Ident.string_of_lid
                                                                    ed.FStarC_Syntax_Syntax.mname in
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Ident.string_of_lid
                                                                    act1.FStarC_Syntax_Syntax.action_name in
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    t in
                                                                    FStarC_Compiler_Util.format3
                                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                                    uu___25
                                                                    uu___26
                                                                    uu___27 in
                                                                    let repr_args
                                                                    t =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    t in
                                                                    uu___26.FStarC_Syntax_Syntax.n in
                                                                    match uu___25
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_app
                                                                    {
                                                                    FStarC_Syntax_Syntax.hd
                                                                    = head;
                                                                    FStarC_Syntax_Syntax.args
                                                                    = a::is;_}
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    head in
                                                                    uu___27.FStarC_Syntax_Syntax.n in
                                                                    (match uu___26
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_uinst
                                                                    (uu___27,
                                                                    us) ->
                                                                    (us,
                                                                    (FStar_Pervasives_Native.fst
                                                                    a), is)
                                                                    | 
                                                                    uu___27
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    err_msg t in
                                                                    FStarC_Errors.raise_error
                                                                    FStarC_Class_HasRange.hasRange_range
                                                                    r
                                                                    FStarC_Errors_Codes.Fatal_ActionMustHaveFunctionType
                                                                    ()
                                                                    (Obj.magic
                                                                    FStarC_Errors_Msg.is_error_message_string)
                                                                    (Obj.magic
                                                                    uu___28))
                                                                    | 
                                                                    uu___26
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    err_msg t in
                                                                    FStarC_Errors.raise_error
                                                                    FStarC_Class_HasRange.hasRange_range
                                                                    r
                                                                    FStarC_Errors_Codes.Fatal_ActionMustHaveFunctionType
                                                                    ()
                                                                    (Obj.magic
                                                                    FStarC_Errors_Msg.is_error_message_string)
                                                                    (Obj.magic
                                                                    uu___27) in
                                                                    let k1 =
                                                                    FStarC_TypeChecker_Normalize.normalize
                                                                    [FStarC_TypeChecker_Env.Beta]
                                                                    env1 k in
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    k1 in
                                                                    uu___26.FStarC_Syntax_Syntax.n in
                                                                    match uu___25
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_arrow
                                                                    {
                                                                    FStarC_Syntax_Syntax.bs1
                                                                    = bs;
                                                                    FStarC_Syntax_Syntax.comp
                                                                    = c;_} ->
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Syntax_Subst.open_comp
                                                                    bs c in
                                                                    (match uu___26
                                                                    with
                                                                    | 
                                                                    (bs1, c1)
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    repr_args
                                                                    (FStarC_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu___27
                                                                    with
                                                                    | 
                                                                    (us, a,
                                                                    is) ->
                                                                    let ct =
                                                                    {
                                                                    FStarC_Syntax_Syntax.comp_univs
                                                                    = us;
                                                                    FStarC_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed.FStarC_Syntax_Syntax.mname);
                                                                    FStarC_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStarC_Syntax_Syntax.effect_args
                                                                    = is;
                                                                    FStarC_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu___28
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_Comp
                                                                    ct in
                                                                    FStarC_Syntax_Util.arrow
                                                                    bs1
                                                                    uu___28))
                                                                    | 
                                                                    uu___26
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    err_msg
                                                                    k1 in
                                                                    FStarC_Errors.raise_error
                                                                    FStarC_Class_HasRange.hasRange_range
                                                                    r
                                                                    FStarC_Errors_Codes.Fatal_ActionMustHaveFunctionType
                                                                    ()
                                                                    (Obj.magic
                                                                    FStarC_Errors_Msg.is_error_message_string)
                                                                    (Obj.magic
                                                                    uu___27) in
                                                                    (
                                                                    let uu___26
                                                                    =
                                                                    (FStarC_Compiler_Debug.medium
                                                                    ()) ||
                                                                    (FStarC_Compiler_Effect.op_Bang
                                                                    dbg_LayeredEffectsTc) in
                                                                    if
                                                                    uu___26
                                                                    then
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    act_typ2 in
                                                                    FStarC_Compiler_Util.print1
                                                                    "Action type after injecting it into the monad: %s\n"
                                                                    uu___27
                                                                    else ());
                                                                    (
                                                                    let act2
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_TypeChecker_Generalize.generalize_universes
                                                                    env1
                                                                    act_defn in
                                                                    match uu___26
                                                                    with
                                                                    | 
                                                                    (us,
                                                                    act_defn1)
                                                                    ->
                                                                    if
                                                                    act1.FStarC_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Syntax_Subst.close_univ_vars
                                                                    us
                                                                    act_typ2 in
                                                                    {
                                                                    FStarC_Syntax_Syntax.action_name
                                                                    =
                                                                    (act1.FStarC_Syntax_Syntax.action_name);
                                                                    FStarC_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (act1.FStarC_Syntax_Syntax.action_unqualified_name);
                                                                    FStarC_Syntax_Syntax.action_univs
                                                                    = us;
                                                                    FStarC_Syntax_Syntax.action_params
                                                                    =
                                                                    (act1.FStarC_Syntax_Syntax.action_params);
                                                                    FStarC_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn1;
                                                                    FStarC_Syntax_Syntax.action_typ
                                                                    = uu___27
                                                                    }
                                                                    else
                                                                    (let uu___28
                                                                    =
                                                                    ((FStarC_Compiler_List.length
                                                                    us) =
                                                                    (FStarC_Compiler_List.length
                                                                    act1.FStarC_Syntax_Syntax.action_univs))
                                                                    &&
                                                                    (FStarC_Compiler_List.forall2
                                                                    (fun u1
                                                                    ->
                                                                    fun u2 ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Syntax_Syntax.order_univ_name
                                                                    u1 u2 in
                                                                    uu___29 =
                                                                    Prims.int_zero)
                                                                    us
                                                                    act1.FStarC_Syntax_Syntax.action_univs) in
                                                                    if
                                                                    uu___28
                                                                    then
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Syntax_Subst.close_univ_vars
                                                                    act1.FStarC_Syntax_Syntax.action_univs
                                                                    act_typ2 in
                                                                    {
                                                                    FStarC_Syntax_Syntax.action_name
                                                                    =
                                                                    (act1.FStarC_Syntax_Syntax.action_name);
                                                                    FStarC_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (act1.FStarC_Syntax_Syntax.action_unqualified_name);
                                                                    FStarC_Syntax_Syntax.action_univs
                                                                    =
                                                                    (act1.FStarC_Syntax_Syntax.action_univs);
                                                                    FStarC_Syntax_Syntax.action_params
                                                                    =
                                                                    (act1.FStarC_Syntax_Syntax.action_params);
                                                                    FStarC_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn1;
                                                                    FStarC_Syntax_Syntax.action_typ
                                                                    = uu___29
                                                                    }
                                                                    else
                                                                    (let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStarC_Ident.string_of_lid
                                                                    ed.FStarC_Syntax_Syntax.mname in
                                                                    let uu___32
                                                                    =
                                                                    FStarC_Ident.string_of_lid
                                                                    act1.FStarC_Syntax_Syntax.action_name in
                                                                    let uu___33
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    (FStarC_Class_Show.show_list
                                                                    FStarC_Ident.showable_ident)
                                                                    us in
                                                                    let uu___34
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    (FStarC_Class_Show.show_list
                                                                    FStarC_Ident.showable_ident)
                                                                    act1.FStarC_Syntax_Syntax.action_univs in
                                                                    FStarC_Compiler_Util.format4
                                                                    "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                    uu___31
                                                                    uu___32
                                                                    uu___33
                                                                    uu___34 in
                                                                    FStarC_Errors.raise_error
                                                                    FStarC_Class_HasRange.hasRange_range
                                                                    r
                                                                    FStarC_Errors_Codes.Fatal_UnexpectedNumberOfUniverse
                                                                    ()
                                                                    (Obj.magic
                                                                    FStarC_Errors_Msg.is_error_message_string)
                                                                    (Obj.magic
                                                                    uu___30))) in
                                                                    act2))))))))) in
                                           let tc_action_with_ctx env act =
                                             let uu___14 =
                                               let uu___15 =
                                                 FStarC_Ident.string_of_lid
                                                   act.FStarC_Syntax_Syntax.action_name in
                                               FStarC_Compiler_Util.format1
                                                 "While checking the action %s"
                                                 uu___15 in
                                             FStarC_Errors.with_ctx uu___14
                                               (fun uu___15 ->
                                                  tc_action env act) in
                                           let extraction_mode =
                                             let has_primitive_extraction =
                                               FStarC_Syntax_Util.has_attribute
                                                 ed.FStarC_Syntax_Syntax.eff_attrs
                                                 FStarC_Parser_Const.primitive_extraction_attr in
                                             let is_reifiable =
                                               FStarC_Compiler_List.contains
                                                 FStarC_Syntax_Syntax.Reifiable
                                                 quals in
                                             if
                                               has_primitive_extraction &&
                                                 is_reifiable
                                             then
                                               let uu___14 =
                                                 let uu___15 =
                                                   FStarC_Class_Show.show
                                                     FStarC_Ident.showable_lident
                                                     ed.FStarC_Syntax_Syntax.mname in
                                                 FStarC_Compiler_Util.format1
                                                   "Effect %s is declared to be both primitive extraction and reifiable"
                                                   uu___15 in
                                               FStarC_Errors.raise_error
                                                 FStarC_Ident.hasrange_lident
                                                 ed.FStarC_Syntax_Syntax.mname
                                                 FStarC_Errors_Codes.Fatal_UnexpectedEffect
                                                 ()
                                                 (Obj.magic
                                                    FStarC_Errors_Msg.is_error_message_string)
                                                 (Obj.magic uu___14)
                                             else
                                               if has_primitive_extraction
                                               then
                                                 FStarC_Syntax_Syntax.Extract_primitive
                                               else
                                                 (let uu___16 =
                                                    let uu___17 =
                                                      let uu___18 = signature in
                                                      match uu___18 with
                                                      | (us, t, uu___19) ->
                                                          (us, t) in
                                                    match uu___17 with
                                                    | (us, t) ->
                                                        let uu___18 =
                                                          let uu___19 =
                                                            FStarC_Syntax_Subst.compress
                                                              t in
                                                          uu___19.FStarC_Syntax_Syntax.n in
                                                        (match uu___18 with
                                                         | FStarC_Syntax_Syntax.Tm_arrow
                                                             {
                                                               FStarC_Syntax_Syntax.bs1
                                                                 = bs;
                                                               FStarC_Syntax_Syntax.comp
                                                                 = uu___19;_}
                                                             ->
                                                             let uu___20 =
                                                               FStarC_Syntax_Subst.open_binders
                                                                 bs in
                                                             (match uu___20
                                                              with
                                                              | a_b::rest_bs
                                                                  ->
                                                                  (us, a_b,
                                                                    rest_bs))
                                                         | uu___19 ->
                                                             failwith
                                                               "Impossible!") in
                                                  match uu___16 with
                                                  | (us, a_b, rest_bs) ->
                                                      let env =
                                                        FStarC_TypeChecker_Env.push_univ_vars
                                                          env0 us in
                                                      let env1 =
                                                        FStarC_TypeChecker_Env.push_binders
                                                          env [a_b] in
                                                      let uu___17 =
                                                        FStarC_Compiler_List.fold_left
                                                          (fun uu___18 ->
                                                             fun b ->
                                                               match uu___18
                                                               with
                                                               | (env2, r) ->
                                                                   let r1 =
                                                                    r &&
                                                                    (FStarC_TypeChecker_Normalize.non_info_norm
                                                                    env2
                                                                    (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort) in
                                                                   let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_Env.push_binders
                                                                    env2 
                                                                    [b] in
                                                                   (uu___19,
                                                                    r1))
                                                          (env1, true)
                                                          rest_bs in
                                                      (match uu___17 with
                                                       | (uu___18, r) ->
                                                           let uu___19 =
                                                             (r &&
                                                                (FStarC_Syntax_Syntax.uu___is_Substitutive_combinator
                                                                   bind_kind))
                                                               &&
                                                               (is_reifiable
                                                                  ||
                                                                  (FStarC_Ident.lid_equals
                                                                    ed.FStarC_Syntax_Syntax.mname
                                                                    FStarC_Parser_Const.effect_TAC_lid)) in
                                                           if uu___19
                                                           then
                                                             FStarC_Syntax_Syntax.Extract_reify
                                                           else
                                                             (let m =
                                                                if
                                                                  Prims.op_Negation
                                                                    r
                                                                then
                                                                  "one or more effect indices are informative"
                                                                else
                                                                  if
                                                                    Prims.op_Negation
                                                                    (FStarC_Syntax_Syntax.uu___is_Substitutive_combinator
                                                                    bind_kind)
                                                                  then
                                                                    "bind is not substitutive"
                                                                  else
                                                                    "the effect is not reifiable" in
                                                              FStarC_Syntax_Syntax.Extract_none
                                                                m))) in
                                           (let uu___15 =
                                              FStarC_Compiler_Effect.op_Bang
                                                dbg_LayeredEffectsTc in
                                            if uu___15
                                            then
                                              let uu___16 =
                                                FStarC_Class_Show.show
                                                  FStarC_Ident.showable_lident
                                                  ed.FStarC_Syntax_Syntax.mname in
                                              let uu___17 =
                                                FStarC_Class_Show.show
                                                  FStarC_Syntax_Syntax.showable_eff_extraction_mode
                                                  extraction_mode in
                                              FStarC_Compiler_Util.print2
                                                "Effect %s has extraction mode %s\n"
                                                uu___16 uu___17
                                            else ());
                                           (let tschemes_of uu___15 k =
                                              match uu___15 with
                                              | (us, t, ty) ->
                                                  ((us, t), (us, ty), k) in
                                            let tschemes_of2 uu___15 =
                                              match uu___15 with
                                              | (us, t, ty) ->
                                                  ((us, t), (us, ty)) in
                                            let combinators =
                                              FStarC_Syntax_Syntax.Layered_eff
                                                {
                                                  FStarC_Syntax_Syntax.l_repr
                                                    = (tschemes_of2 repr);
                                                  FStarC_Syntax_Syntax.l_return
                                                    =
                                                    (tschemes_of2 return_repr);
                                                  FStarC_Syntax_Syntax.l_bind
                                                    =
                                                    (tschemes_of bind_repr
                                                       (FStar_Pervasives_Native.Some
                                                          bind_kind));
                                                  FStarC_Syntax_Syntax.l_subcomp
                                                    =
                                                    (tschemes_of
                                                       stronger_repr
                                                       (FStar_Pervasives_Native.Some
                                                          subcomp_kind));
                                                  FStarC_Syntax_Syntax.l_if_then_else
                                                    =
                                                    (tschemes_of if_then_else
                                                       (FStar_Pervasives_Native.Some
                                                          ite_kind));
                                                  FStarC_Syntax_Syntax.l_close
                                                    =
                                                    (match close_ with
                                                     | FStar_Pervasives_Native.None
                                                         ->
                                                         FStar_Pervasives_Native.None
                                                     | FStar_Pervasives_Native.Some
                                                         (us, t, ty) ->
                                                         FStar_Pervasives_Native.Some
                                                           ((us, t),
                                                             (us, ty)))
                                                } in
                                            let uu___15 =
                                              FStarC_Compiler_List.map
                                                (tc_action_with_ctx env0)
                                                ed.FStarC_Syntax_Syntax.actions in
                                            {
                                              FStarC_Syntax_Syntax.mname =
                                                (ed.FStarC_Syntax_Syntax.mname);
                                              FStarC_Syntax_Syntax.cattributes
                                                =
                                                (ed.FStarC_Syntax_Syntax.cattributes);
                                              FStarC_Syntax_Syntax.univs =
                                                (ed.FStarC_Syntax_Syntax.univs);
                                              FStarC_Syntax_Syntax.binders =
                                                (ed.FStarC_Syntax_Syntax.binders);
                                              FStarC_Syntax_Syntax.signature
                                                =
                                                (FStarC_Syntax_Syntax.Layered_eff_sig
                                                   (num_effect_params,
                                                     (let uu___16 = signature in
                                                      match uu___16 with
                                                      | (us, t, uu___17) ->
                                                          (us, t))));
                                              FStarC_Syntax_Syntax.combinators
                                                = combinators;
                                              FStarC_Syntax_Syntax.actions =
                                                uu___15;
                                              FStarC_Syntax_Syntax.eff_attrs
                                                =
                                                (ed.FStarC_Syntax_Syntax.eff_attrs);
                                              FStarC_Syntax_Syntax.extraction_mode
                                                = extraction_mode
                                            }))))))))))))))
let (tc_non_layered_eff_decl :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.eff_decl ->
      FStarC_Syntax_Syntax.qualifier Prims.list ->
        FStarC_Syntax_Syntax.attribute Prims.list ->
          FStarC_Syntax_Syntax.eff_decl)
  =
  fun env0 ->
    fun ed ->
      fun _quals ->
        fun _attrs ->
          let uu___ =
            let uu___1 =
              FStarC_Ident.string_of_lid ed.FStarC_Syntax_Syntax.mname in
            FStarC_Compiler_Util.format1
              "While checking effect definition `%s`" uu___1 in
          FStarC_Errors.with_ctx uu___
            (fun uu___1 ->
               (let uu___3 = FStarC_Compiler_Effect.op_Bang dbg in
                if uu___3
                then
                  let uu___4 =
                    FStarC_Class_Show.show
                      FStarC_Syntax_Print.showable_eff_decl ed in
                  FStarC_Compiler_Util.print1
                    "Typechecking eff_decl: \n\t%s\n" uu___4
                else ());
               (let uu___3 =
                  let uu___4 =
                    FStarC_Syntax_Subst.univ_var_opening
                      ed.FStarC_Syntax_Syntax.univs in
                  match uu___4 with
                  | (ed_univs_subst, ed_univs) ->
                      let bs =
                        let uu___5 =
                          FStarC_Syntax_Subst.subst_binders ed_univs_subst
                            ed.FStarC_Syntax_Syntax.binders in
                        FStarC_Syntax_Subst.open_binders uu___5 in
                      let uu___5 =
                        let uu___6 =
                          FStarC_TypeChecker_Env.push_univ_vars env0 ed_univs in
                        FStarC_TypeChecker_TcTerm.tc_tparams uu___6 bs in
                      (match uu___5 with
                       | (bs1, uu___6, uu___7) ->
                           let uu___8 =
                             let tmp_t =
                               let uu___9 =
                                 FStarC_Syntax_Syntax.mk_Total
                                   FStarC_Syntax_Syntax.t_unit in
                               FStarC_Syntax_Util.arrow bs1 uu___9 in
                             let uu___9 =
                               FStarC_TypeChecker_Generalize.generalize_universes
                                 env0 tmp_t in
                             match uu___9 with
                             | (us, tmp_t1) ->
                                 let uu___10 =
                                   let uu___11 =
                                     let uu___12 =
                                       FStarC_Syntax_Util.arrow_formals
                                         tmp_t1 in
                                     FStar_Pervasives_Native.fst uu___12 in
                                   FStarC_Syntax_Subst.close_binders uu___11 in
                                 (us, uu___10) in
                           (match uu___8 with
                            | (us, bs2) ->
                                (match ed_univs with
                                 | [] -> (us, bs2)
                                 | uu___9 ->
                                     let uu___10 =
                                       ((FStarC_Compiler_List.length ed_univs)
                                          = (FStarC_Compiler_List.length us))
                                         &&
                                         (FStarC_Compiler_List.forall2
                                            (fun u1 ->
                                               fun u2 ->
                                                 let uu___11 =
                                                   FStarC_Syntax_Syntax.order_univ_name
                                                     u1 u2 in
                                                 uu___11 = Prims.int_zero)
                                            ed_univs us) in
                                     if uu___10
                                     then (us, bs2)
                                     else
                                       (let uu___12 =
                                          let uu___13 =
                                            let uu___14 =
                                              FStarC_Errors_Msg.text
                                                "Expected and generalized universes in effect declaration for" in
                                            let uu___15 =
                                              let uu___16 =
                                                let uu___17 =
                                                  FStarC_Ident.string_of_lid
                                                    ed.FStarC_Syntax_Syntax.mname in
                                                FStarC_Pprint.doc_of_string
                                                  uu___17 in
                                              let uu___17 =
                                                FStarC_Errors_Msg.text
                                                  "are different" in
                                              FStarC_Pprint.op_Hat_Slash_Hat
                                                uu___16 uu___17 in
                                            FStarC_Pprint.op_Hat_Slash_Hat
                                              uu___14 uu___15 in
                                          let uu___14 =
                                            let uu___15 =
                                              let uu___16 =
                                                FStarC_Errors_Msg.text
                                                  "Expected" in
                                              let uu___17 =
                                                let uu___18 =
                                                  FStarC_Class_PP.pp
                                                    FStarC_Class_PP.pp_int
                                                    (FStarC_Compiler_List.length
                                                       ed_univs) in
                                                let uu___19 =
                                                  let uu___20 =
                                                    FStarC_Errors_Msg.text
                                                      "but found" in
                                                  let uu___21 =
                                                    FStarC_Class_PP.pp
                                                      FStarC_Class_PP.pp_int
                                                      (FStarC_Compiler_List.length
                                                         us) in
                                                  FStarC_Pprint.op_Hat_Slash_Hat
                                                    uu___20 uu___21 in
                                                FStarC_Pprint.op_Hat_Slash_Hat
                                                  uu___18 uu___19 in
                                              FStarC_Pprint.op_Hat_Slash_Hat
                                                uu___16 uu___17 in
                                            [uu___15] in
                                          uu___13 :: uu___14 in
                                        FStarC_Errors.raise_error
                                          FStarC_Ident.hasrange_lident
                                          ed.FStarC_Syntax_Syntax.mname
                                          FStarC_Errors_Codes.Fatal_UnexpectedNumberOfUniverse
                                          ()
                                          (Obj.magic
                                             FStarC_Errors_Msg.is_error_message_list_doc)
                                          (Obj.magic uu___12))))) in
                match uu___3 with
                | (us, bs) ->
                    let ed1 =
                      {
                        FStarC_Syntax_Syntax.mname =
                          (ed.FStarC_Syntax_Syntax.mname);
                        FStarC_Syntax_Syntax.cattributes =
                          (ed.FStarC_Syntax_Syntax.cattributes);
                        FStarC_Syntax_Syntax.univs = us;
                        FStarC_Syntax_Syntax.binders = bs;
                        FStarC_Syntax_Syntax.signature =
                          (ed.FStarC_Syntax_Syntax.signature);
                        FStarC_Syntax_Syntax.combinators =
                          (ed.FStarC_Syntax_Syntax.combinators);
                        FStarC_Syntax_Syntax.actions =
                          (ed.FStarC_Syntax_Syntax.actions);
                        FStarC_Syntax_Syntax.eff_attrs =
                          (ed.FStarC_Syntax_Syntax.eff_attrs);
                        FStarC_Syntax_Syntax.extraction_mode =
                          (ed.FStarC_Syntax_Syntax.extraction_mode)
                      } in
                    let uu___4 = FStarC_Syntax_Subst.univ_var_opening us in
                    (match uu___4 with
                     | (ed_univs_subst, ed_univs) ->
                         let uu___5 =
                           let uu___6 =
                             FStarC_Syntax_Subst.subst_binders ed_univs_subst
                               bs in
                           FStarC_Syntax_Subst.open_binders' uu___6 in
                         (match uu___5 with
                          | (ed_bs, ed_bs_subst) ->
                              let ed2 =
                                let op uu___6 =
                                  match uu___6 with
                                  | (us1, t) ->
                                      let t1 =
                                        let uu___7 =
                                          FStarC_Syntax_Subst.shift_subst
                                            ((FStarC_Compiler_List.length
                                                ed_bs)
                                               +
                                               (FStarC_Compiler_List.length
                                                  us1)) ed_univs_subst in
                                        FStarC_Syntax_Subst.subst uu___7 t in
                                      let uu___7 =
                                        let uu___8 =
                                          FStarC_Syntax_Subst.shift_subst
                                            (FStarC_Compiler_List.length us1)
                                            ed_bs_subst in
                                        FStarC_Syntax_Subst.subst uu___8 t1 in
                                      (us1, uu___7) in
                                let uu___6 =
                                  FStarC_Syntax_Util.apply_eff_sig op
                                    ed1.FStarC_Syntax_Syntax.signature in
                                let uu___7 =
                                  FStarC_Syntax_Util.apply_eff_combinators op
                                    ed1.FStarC_Syntax_Syntax.combinators in
                                let uu___8 =
                                  FStarC_Compiler_List.map
                                    (fun a ->
                                       let uu___9 =
                                         let uu___10 =
                                           op
                                             ((a.FStarC_Syntax_Syntax.action_univs),
                                               (a.FStarC_Syntax_Syntax.action_defn)) in
                                         FStar_Pervasives_Native.snd uu___10 in
                                       let uu___10 =
                                         let uu___11 =
                                           op
                                             ((a.FStarC_Syntax_Syntax.action_univs),
                                               (a.FStarC_Syntax_Syntax.action_typ)) in
                                         FStar_Pervasives_Native.snd uu___11 in
                                       {
                                         FStarC_Syntax_Syntax.action_name =
                                           (a.FStarC_Syntax_Syntax.action_name);
                                         FStarC_Syntax_Syntax.action_unqualified_name
                                           =
                                           (a.FStarC_Syntax_Syntax.action_unqualified_name);
                                         FStarC_Syntax_Syntax.action_univs =
                                           (a.FStarC_Syntax_Syntax.action_univs);
                                         FStarC_Syntax_Syntax.action_params =
                                           (a.FStarC_Syntax_Syntax.action_params);
                                         FStarC_Syntax_Syntax.action_defn =
                                           uu___9;
                                         FStarC_Syntax_Syntax.action_typ =
                                           uu___10
                                       }) ed1.FStarC_Syntax_Syntax.actions in
                                {
                                  FStarC_Syntax_Syntax.mname =
                                    (ed1.FStarC_Syntax_Syntax.mname);
                                  FStarC_Syntax_Syntax.cattributes =
                                    (ed1.FStarC_Syntax_Syntax.cattributes);
                                  FStarC_Syntax_Syntax.univs =
                                    (ed1.FStarC_Syntax_Syntax.univs);
                                  FStarC_Syntax_Syntax.binders =
                                    (ed1.FStarC_Syntax_Syntax.binders);
                                  FStarC_Syntax_Syntax.signature = uu___6;
                                  FStarC_Syntax_Syntax.combinators = uu___7;
                                  FStarC_Syntax_Syntax.actions = uu___8;
                                  FStarC_Syntax_Syntax.eff_attrs =
                                    (ed1.FStarC_Syntax_Syntax.eff_attrs);
                                  FStarC_Syntax_Syntax.extraction_mode =
                                    (ed1.FStarC_Syntax_Syntax.extraction_mode)
                                } in
                              ((let uu___7 =
                                  FStarC_Compiler_Effect.op_Bang dbg in
                                if uu___7
                                then
                                  let uu___8 =
                                    FStarC_Class_Show.show
                                      FStarC_Syntax_Print.showable_eff_decl
                                      ed2 in
                                  FStarC_Compiler_Util.print1
                                    "After typechecking binders eff_decl: \n\t%s\n"
                                    uu___8
                                else ());
                               (let env =
                                  let uu___7 =
                                    FStarC_TypeChecker_Env.push_univ_vars
                                      env0 ed_univs in
                                  FStarC_TypeChecker_Env.push_binders uu___7
                                    ed_bs in
                                let check_and_gen' comb n env_opt uu___7 k =
                                  match uu___7 with
                                  | (us1, t) ->
                                      let env1 =
                                        if
                                          FStarC_Compiler_Util.is_some
                                            env_opt
                                        then
                                          FStarC_Compiler_Util.must env_opt
                                        else env in
                                      let uu___8 =
                                        FStarC_Syntax_Subst.open_univ_vars
                                          us1 t in
                                      (match uu___8 with
                                       | (us2, t1) ->
                                           let t2 =
                                             match k with
                                             | FStar_Pervasives_Native.Some
                                                 k1 ->
                                                 let uu___9 =
                                                   FStarC_TypeChecker_Env.push_univ_vars
                                                     env1 us2 in
                                                 FStarC_TypeChecker_TcTerm.tc_check_trivial_guard
                                                   uu___9 t1 k1
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 let uu___9 =
                                                   let uu___10 =
                                                     FStarC_TypeChecker_Env.push_univ_vars
                                                       env1 us2 in
                                                   FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                     uu___10 t1 in
                                                 (match uu___9 with
                                                  | (t3, uu___10, g) ->
                                                      (FStarC_TypeChecker_Rel.force_trivial_guard
                                                         env1 g;
                                                       t3)) in
                                           let uu___9 =
                                             FStarC_TypeChecker_Generalize.generalize_universes
                                               env1 t2 in
                                           (match uu___9 with
                                            | (g_us, t3) ->
                                                (if
                                                   (FStarC_Compiler_List.length
                                                      g_us)
                                                     <> n
                                                 then
                                                   (let error =
                                                      let uu___11 =
                                                        FStarC_Ident.string_of_lid
                                                          ed2.FStarC_Syntax_Syntax.mname in
                                                      let uu___12 =
                                                        FStarC_Compiler_Util.string_of_int
                                                          n in
                                                      let uu___13 =
                                                        FStarC_Compiler_Util.string_of_int
                                                          (FStarC_Compiler_List.length
                                                             g_us) in
                                                      FStarC_Compiler_Util.format4
                                                        "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                        uu___11 comb uu___12
                                                        uu___13 in
                                                    FStarC_Errors.raise_error
                                                      (FStarC_Syntax_Syntax.has_range_syntax
                                                         ()) t3
                                                      FStarC_Errors_Codes.Fatal_MismatchUniversePolymorphic
                                                      ()
                                                      (Obj.magic
                                                         FStarC_Errors_Msg.is_error_message_string)
                                                      (Obj.magic error))
                                                 else ();
                                                 (match us2 with
                                                  | [] -> (g_us, t3)
                                                  | uu___11 ->
                                                      let uu___12 =
                                                        ((FStarC_Compiler_List.length
                                                            us2)
                                                           =
                                                           (FStarC_Compiler_List.length
                                                              g_us))
                                                          &&
                                                          (FStarC_Compiler_List.forall2
                                                             (fun u1 ->
                                                                fun u2 ->
                                                                  let uu___13
                                                                    =
                                                                    FStarC_Syntax_Syntax.order_univ_name
                                                                    u1 u2 in
                                                                  uu___13 =
                                                                    Prims.int_zero)
                                                             us2 g_us) in
                                                      if uu___12
                                                      then (g_us, t3)
                                                      else
                                                        (let uu___14 =
                                                           let uu___15 =
                                                             FStarC_Ident.string_of_lid
                                                               ed2.FStarC_Syntax_Syntax.mname in
                                                           let uu___16 =
                                                             FStarC_Compiler_Util.string_of_int
                                                               (FStarC_Compiler_List.length
                                                                  us2) in
                                                           let uu___17 =
                                                             FStarC_Compiler_Util.string_of_int
                                                               (FStarC_Compiler_List.length
                                                                  g_us) in
                                                           FStarC_Compiler_Util.format4
                                                             "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                             uu___15 comb
                                                             uu___16 uu___17 in
                                                         FStarC_Errors.raise_error
                                                           (FStarC_Syntax_Syntax.has_range_syntax
                                                              ()) t3
                                                           FStarC_Errors_Codes.Fatal_UnexpectedNumberOfUniverse
                                                           ()
                                                           (Obj.magic
                                                              FStarC_Errors_Msg.is_error_message_string)
                                                           (Obj.magic uu___14)))))) in
                                let signature =
                                  let uu___7 =
                                    FStarC_Syntax_Util.effect_sig_ts
                                      ed2.FStarC_Syntax_Syntax.signature in
                                  check_and_gen' "signature" Prims.int_one
                                    FStar_Pervasives_Native.None uu___7
                                    FStar_Pervasives_Native.None in
                                (let uu___8 =
                                   FStarC_Compiler_Effect.op_Bang dbg in
                                 if uu___8
                                 then
                                   let uu___9 =
                                     FStarC_Syntax_Print.tscheme_to_string
                                       signature in
                                   FStarC_Compiler_Util.print1
                                     "Typechecked signature: %s\n" uu___9
                                 else ());
                                (let fresh_a_and_wp uu___8 =
                                   let fail t =
                                     let uu___9 =
                                       let uu___10 =
                                         let uu___11 =
                                           FStarC_Syntax_Util.effect_sig_ts
                                             ed2.FStarC_Syntax_Syntax.signature in
                                         FStar_Pervasives_Native.snd uu___11 in
                                       uu___10.FStarC_Syntax_Syntax.pos in
                                     FStarC_TypeChecker_Err.unexpected_signature_for_monad
                                       env uu___9
                                       ed2.FStarC_Syntax_Syntax.mname t in
                                   let uu___9 =
                                     FStarC_TypeChecker_Env.inst_tscheme
                                       signature in
                                   match uu___9 with
                                   | (uu___10, signature1) ->
                                       let uu___11 =
                                         let uu___12 =
                                           FStarC_Syntax_Subst.compress
                                             signature1 in
                                         uu___12.FStarC_Syntax_Syntax.n in
                                       (match uu___11 with
                                        | FStarC_Syntax_Syntax.Tm_arrow
                                            { FStarC_Syntax_Syntax.bs1 = bs1;
                                              FStarC_Syntax_Syntax.comp =
                                                uu___12;_}
                                            ->
                                            let bs2 =
                                              FStarC_Syntax_Subst.open_binders
                                                bs1 in
                                            (match bs2 with
                                             | {
                                                 FStarC_Syntax_Syntax.binder_bv
                                                   = a;
                                                 FStarC_Syntax_Syntax.binder_qual
                                                   = uu___13;
                                                 FStarC_Syntax_Syntax.binder_positivity
                                                   = uu___14;
                                                 FStarC_Syntax_Syntax.binder_attrs
                                                   = uu___15;_}::{
                                                                   FStarC_Syntax_Syntax.binder_bv
                                                                    = wp;
                                                                   FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___16;
                                                                   FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___17;
                                                                   FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___18;_}::[]
                                                 ->
                                                 (a,
                                                   (wp.FStarC_Syntax_Syntax.sort))
                                             | uu___13 -> fail signature1)
                                        | uu___12 -> fail signature1) in
                                 let log_combinator s ts =
                                   let uu___8 =
                                     FStarC_Compiler_Effect.op_Bang dbg in
                                   if uu___8
                                   then
                                     let uu___9 =
                                       FStarC_Ident.string_of_lid
                                         ed2.FStarC_Syntax_Syntax.mname in
                                     let uu___10 =
                                       FStarC_Syntax_Print.tscheme_to_string
                                         ts in
                                     FStarC_Compiler_Util.print3
                                       "Typechecked %s:%s = %s\n" uu___9 s
                                       uu___10
                                   else () in
                                 let ret_wp =
                                   let uu___8 = fresh_a_and_wp () in
                                   match uu___8 with
                                   | (a, wp_sort) ->
                                       let k =
                                         let uu___9 =
                                           let uu___10 =
                                             FStarC_Syntax_Syntax.mk_binder a in
                                           let uu___11 =
                                             let uu___12 =
                                               let uu___13 =
                                                 FStarC_Syntax_Syntax.bv_to_name
                                                   a in
                                               FStarC_Syntax_Syntax.null_binder
                                                 uu___13 in
                                             [uu___12] in
                                           uu___10 :: uu___11 in
                                         let uu___10 =
                                           FStarC_Syntax_Syntax.mk_GTotal
                                             wp_sort in
                                         FStarC_Syntax_Util.arrow uu___9
                                           uu___10 in
                                       let uu___9 =
                                         FStarC_Syntax_Util.get_return_vc_combinator
                                           ed2 in
                                       check_and_gen' "ret_wp" Prims.int_one
                                         FStar_Pervasives_Native.None uu___9
                                         (FStar_Pervasives_Native.Some k) in
                                 log_combinator "ret_wp" ret_wp;
                                 (let bind_wp =
                                    let uu___9 = fresh_a_and_wp () in
                                    match uu___9 with
                                    | (a, wp_sort_a) ->
                                        let uu___10 = fresh_a_and_wp () in
                                        (match uu___10 with
                                         | (b, wp_sort_b) ->
                                             let wp_sort_a_b =
                                               let uu___11 =
                                                 let uu___12 =
                                                   let uu___13 =
                                                     FStarC_Syntax_Syntax.bv_to_name
                                                       a in
                                                   FStarC_Syntax_Syntax.null_binder
                                                     uu___13 in
                                                 [uu___12] in
                                               let uu___12 =
                                                 FStarC_Syntax_Syntax.mk_Total
                                                   wp_sort_b in
                                               FStarC_Syntax_Util.arrow
                                                 uu___11 uu___12 in
                                             let k =
                                               let uu___11 =
                                                 let uu___12 =
                                                   FStarC_Syntax_Syntax.mk_binder
                                                     a in
                                                 let uu___13 =
                                                   let uu___14 =
                                                     FStarC_Syntax_Syntax.mk_binder
                                                       b in
                                                   let uu___15 =
                                                     let uu___16 =
                                                       FStarC_Syntax_Syntax.null_binder
                                                         wp_sort_a in
                                                     let uu___17 =
                                                       let uu___18 =
                                                         FStarC_Syntax_Syntax.null_binder
                                                           wp_sort_a_b in
                                                       [uu___18] in
                                                     uu___16 :: uu___17 in
                                                   uu___14 :: uu___15 in
                                                 uu___12 :: uu___13 in
                                               let uu___12 =
                                                 FStarC_Syntax_Syntax.mk_Total
                                                   wp_sort_b in
                                               FStarC_Syntax_Util.arrow
                                                 uu___11 uu___12 in
                                             let uu___11 =
                                               let uu___12 =
                                                 FStarC_Syntax_Util.get_bind_vc_combinator
                                                   ed2 in
                                               FStar_Pervasives_Native.fst
                                                 uu___12 in
                                             check_and_gen' "bind_wp"
                                               (Prims.of_int (2))
                                               FStar_Pervasives_Native.None
                                               uu___11
                                               (FStar_Pervasives_Native.Some
                                                  k)) in
                                  log_combinator "bind_wp" bind_wp;
                                  (let stronger =
                                     let uu___10 = fresh_a_and_wp () in
                                     match uu___10 with
                                     | (a, wp_sort_a) ->
                                         let uu___11 =
                                           FStarC_Syntax_Util.type_u () in
                                         (match uu___11 with
                                          | (t, uu___12) ->
                                              let k =
                                                let uu___13 =
                                                  let uu___14 =
                                                    FStarC_Syntax_Syntax.mk_binder
                                                      a in
                                                  let uu___15 =
                                                    let uu___16 =
                                                      FStarC_Syntax_Syntax.null_binder
                                                        wp_sort_a in
                                                    let uu___17 =
                                                      let uu___18 =
                                                        FStarC_Syntax_Syntax.null_binder
                                                          wp_sort_a in
                                                      [uu___18] in
                                                    uu___16 :: uu___17 in
                                                  uu___14 :: uu___15 in
                                                let uu___14 =
                                                  FStarC_Syntax_Syntax.mk_Total
                                                    t in
                                                FStarC_Syntax_Util.arrow
                                                  uu___13 uu___14 in
                                              let uu___13 =
                                                let uu___14 =
                                                  FStarC_Syntax_Util.get_stronger_vc_combinator
                                                    ed2 in
                                                FStar_Pervasives_Native.fst
                                                  uu___14 in
                                              check_and_gen' "stronger"
                                                Prims.int_one
                                                FStar_Pervasives_Native.None
                                                uu___13
                                                (FStar_Pervasives_Native.Some
                                                   k)) in
                                   log_combinator "stronger" stronger;
                                   (let if_then_else =
                                      let uu___11 = fresh_a_and_wp () in
                                      match uu___11 with
                                      | (a, wp_sort_a) ->
                                          let p =
                                            let uu___12 =
                                              let uu___13 =
                                                FStarC_Ident.range_of_lid
                                                  ed2.FStarC_Syntax_Syntax.mname in
                                              FStar_Pervasives_Native.Some
                                                uu___13 in
                                            let uu___13 =
                                              let uu___14 =
                                                FStarC_Syntax_Util.type_u () in
                                              FStar_Pervasives_Native.fst
                                                uu___14 in
                                            FStarC_Syntax_Syntax.new_bv
                                              uu___12 uu___13 in
                                          let k =
                                            let uu___12 =
                                              let uu___13 =
                                                FStarC_Syntax_Syntax.mk_binder
                                                  a in
                                              let uu___14 =
                                                let uu___15 =
                                                  FStarC_Syntax_Syntax.mk_binder
                                                    p in
                                                let uu___16 =
                                                  let uu___17 =
                                                    FStarC_Syntax_Syntax.null_binder
                                                      wp_sort_a in
                                                  let uu___18 =
                                                    let uu___19 =
                                                      FStarC_Syntax_Syntax.null_binder
                                                        wp_sort_a in
                                                    [uu___19] in
                                                  uu___17 :: uu___18 in
                                                uu___15 :: uu___16 in
                                              uu___13 :: uu___14 in
                                            let uu___13 =
                                              FStarC_Syntax_Syntax.mk_Total
                                                wp_sort_a in
                                            FStarC_Syntax_Util.arrow uu___12
                                              uu___13 in
                                          let uu___12 =
                                            let uu___13 =
                                              FStarC_Syntax_Util.get_wp_if_then_else_combinator
                                                ed2 in
                                            FStarC_Compiler_Util.must uu___13 in
                                          check_and_gen' "if_then_else"
                                            Prims.int_one
                                            FStar_Pervasives_Native.None
                                            uu___12
                                            (FStar_Pervasives_Native.Some k) in
                                    log_combinator "if_then_else"
                                      if_then_else;
                                    (let ite_wp =
                                       let uu___12 = fresh_a_and_wp () in
                                       match uu___12 with
                                       | (a, wp_sort_a) ->
                                           let k =
                                             let uu___13 =
                                               let uu___14 =
                                                 FStarC_Syntax_Syntax.mk_binder
                                                   a in
                                               let uu___15 =
                                                 let uu___16 =
                                                   FStarC_Syntax_Syntax.null_binder
                                                     wp_sort_a in
                                                 [uu___16] in
                                               uu___14 :: uu___15 in
                                             let uu___14 =
                                               FStarC_Syntax_Syntax.mk_Total
                                                 wp_sort_a in
                                             FStarC_Syntax_Util.arrow uu___13
                                               uu___14 in
                                           let uu___13 =
                                             let uu___14 =
                                               FStarC_Syntax_Util.get_wp_ite_combinator
                                                 ed2 in
                                             FStarC_Compiler_Util.must
                                               uu___14 in
                                           check_and_gen' "ite_wp"
                                             Prims.int_one
                                             FStar_Pervasives_Native.None
                                             uu___13
                                             (FStar_Pervasives_Native.Some k) in
                                     log_combinator "ite_wp" ite_wp;
                                     (let close_wp =
                                        let uu___13 = fresh_a_and_wp () in
                                        match uu___13 with
                                        | (a, wp_sort_a) ->
                                            let b =
                                              let uu___14 =
                                                let uu___15 =
                                                  FStarC_Ident.range_of_lid
                                                    ed2.FStarC_Syntax_Syntax.mname in
                                                FStar_Pervasives_Native.Some
                                                  uu___15 in
                                              let uu___15 =
                                                let uu___16 =
                                                  FStarC_Syntax_Util.type_u
                                                    () in
                                                FStar_Pervasives_Native.fst
                                                  uu___16 in
                                              FStarC_Syntax_Syntax.new_bv
                                                uu___14 uu___15 in
                                            let wp_sort_b_a =
                                              let uu___14 =
                                                let uu___15 =
                                                  let uu___16 =
                                                    FStarC_Syntax_Syntax.bv_to_name
                                                      b in
                                                  FStarC_Syntax_Syntax.null_binder
                                                    uu___16 in
                                                [uu___15] in
                                              let uu___15 =
                                                FStarC_Syntax_Syntax.mk_Total
                                                  wp_sort_a in
                                              FStarC_Syntax_Util.arrow
                                                uu___14 uu___15 in
                                            let k =
                                              let uu___14 =
                                                let uu___15 =
                                                  FStarC_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu___16 =
                                                  let uu___17 =
                                                    FStarC_Syntax_Syntax.mk_binder
                                                      b in
                                                  let uu___18 =
                                                    let uu___19 =
                                                      FStarC_Syntax_Syntax.null_binder
                                                        wp_sort_b_a in
                                                    [uu___19] in
                                                  uu___17 :: uu___18 in
                                                uu___15 :: uu___16 in
                                              let uu___15 =
                                                FStarC_Syntax_Syntax.mk_Total
                                                  wp_sort_a in
                                              FStarC_Syntax_Util.arrow
                                                uu___14 uu___15 in
                                            let uu___14 =
                                              let uu___15 =
                                                FStarC_Syntax_Util.get_wp_close_combinator
                                                  ed2 in
                                              FStarC_Compiler_Util.must
                                                uu___15 in
                                            check_and_gen' "close_wp"
                                              (Prims.of_int (2))
                                              FStar_Pervasives_Native.None
                                              uu___14
                                              (FStar_Pervasives_Native.Some k) in
                                      log_combinator "close_wp" close_wp;
                                      (let trivial =
                                         let uu___14 = fresh_a_and_wp () in
                                         match uu___14 with
                                         | (a, wp_sort_a) ->
                                             let uu___15 =
                                               FStarC_Syntax_Util.type_u () in
                                             (match uu___15 with
                                              | (t, uu___16) ->
                                                  let k =
                                                    let uu___17 =
                                                      let uu___18 =
                                                        FStarC_Syntax_Syntax.mk_binder
                                                          a in
                                                      let uu___19 =
                                                        let uu___20 =
                                                          FStarC_Syntax_Syntax.null_binder
                                                            wp_sort_a in
                                                        [uu___20] in
                                                      uu___18 :: uu___19 in
                                                    let uu___18 =
                                                      FStarC_Syntax_Syntax.mk_GTotal
                                                        t in
                                                    FStarC_Syntax_Util.arrow
                                                      uu___17 uu___18 in
                                                  let trivial1 =
                                                    let uu___17 =
                                                      let uu___18 =
                                                        FStarC_Syntax_Util.get_wp_trivial_combinator
                                                          ed2 in
                                                      FStarC_Compiler_Util.must
                                                        uu___18 in
                                                    check_and_gen' "trivial"
                                                      Prims.int_one
                                                      FStar_Pervasives_Native.None
                                                      uu___17
                                                      (FStar_Pervasives_Native.Some
                                                         k) in
                                                  (log_combinator "trivial"
                                                     trivial1;
                                                   trivial1)) in
                                       let uu___14 =
                                         let uu___15 =
                                           FStarC_Syntax_Util.get_eff_repr
                                             ed2 in
                                         match uu___15 with
                                         | FStar_Pervasives_Native.None ->
                                             (FStar_Pervasives_Native.None,
                                               FStar_Pervasives_Native.None,
                                               FStar_Pervasives_Native.None,
                                               (ed2.FStarC_Syntax_Syntax.actions))
                                         | uu___16 ->
                                             let repr =
                                               let uu___17 =
                                                 fresh_a_and_wp () in
                                               match uu___17 with
                                               | (a, wp_sort_a) ->
                                                   let uu___18 =
                                                     FStarC_Syntax_Util.type_u
                                                       () in
                                                   (match uu___18 with
                                                    | (t, uu___19) ->
                                                        let k =
                                                          let uu___20 =
                                                            let uu___21 =
                                                              FStarC_Syntax_Syntax.mk_binder
                                                                a in
                                                            let uu___22 =
                                                              let uu___23 =
                                                                FStarC_Syntax_Syntax.null_binder
                                                                  wp_sort_a in
                                                              [uu___23] in
                                                            uu___21 ::
                                                              uu___22 in
                                                          let uu___21 =
                                                            FStarC_Syntax_Syntax.mk_GTotal
                                                              t in
                                                          FStarC_Syntax_Util.arrow
                                                            uu___20 uu___21 in
                                                        let uu___20 =
                                                          let uu___21 =
                                                            FStarC_Syntax_Util.get_eff_repr
                                                              ed2 in
                                                          FStarC_Compiler_Util.must
                                                            uu___21 in
                                                        check_and_gen' "repr"
                                                          Prims.int_one
                                                          FStar_Pervasives_Native.None
                                                          uu___20
                                                          (FStar_Pervasives_Native.Some
                                                             k)) in
                                             (log_combinator "repr" repr;
                                              (let mk_repr' t wp =
                                                 let uu___18 =
                                                   FStarC_TypeChecker_Env.inst_tscheme
                                                     repr in
                                                 match uu___18 with
                                                 | (uu___19, repr1) ->
                                                     let repr2 =
                                                       FStarC_TypeChecker_Normalize.normalize
                                                         [FStarC_TypeChecker_Env.EraseUniverses;
                                                         FStarC_TypeChecker_Env.AllowUnboundUniverses]
                                                         env repr1 in
                                                     let uu___20 =
                                                       let uu___21 =
                                                         let uu___22 =
                                                           let uu___23 =
                                                             FStarC_Syntax_Syntax.as_arg
                                                               t in
                                                           let uu___24 =
                                                             let uu___25 =
                                                               FStarC_Syntax_Syntax.as_arg
                                                                 wp in
                                                             [uu___25] in
                                                           uu___23 :: uu___24 in
                                                         {
                                                           FStarC_Syntax_Syntax.hd
                                                             = repr2;
                                                           FStarC_Syntax_Syntax.args
                                                             = uu___22
                                                         } in
                                                       FStarC_Syntax_Syntax.Tm_app
                                                         uu___21 in
                                                     FStarC_Syntax_Syntax.mk
                                                       uu___20
                                                       FStarC_Compiler_Range_Type.dummyRange in
                                               let mk_repr a wp =
                                                 let uu___18 =
                                                   FStarC_Syntax_Syntax.bv_to_name
                                                     a in
                                                 mk_repr' uu___18 wp in
                                               let destruct_repr t =
                                                 let uu___18 =
                                                   let uu___19 =
                                                     FStarC_Syntax_Subst.compress
                                                       t in
                                                   uu___19.FStarC_Syntax_Syntax.n in
                                                 match uu___18 with
                                                 | FStarC_Syntax_Syntax.Tm_app
                                                     {
                                                       FStarC_Syntax_Syntax.hd
                                                         = uu___19;
                                                       FStarC_Syntax_Syntax.args
                                                         =
                                                         (t1, uu___20)::
                                                         (wp, uu___21)::[];_}
                                                     -> (t1, wp)
                                                 | uu___19 ->
                                                     failwith
                                                       "Unexpected repr type" in
                                               let return_repr =
                                                 let return_repr_ts =
                                                   let uu___18 =
                                                     FStarC_Syntax_Util.get_return_repr
                                                       ed2 in
                                                   FStarC_Compiler_Util.must
                                                     uu___18 in
                                                 let uu___18 =
                                                   fresh_a_and_wp () in
                                                 match uu___18 with
                                                 | (a, uu___19) ->
                                                     let x_a =
                                                       let uu___20 =
                                                         FStarC_Syntax_Syntax.bv_to_name
                                                           a in
                                                       FStarC_Syntax_Syntax.gen_bv
                                                         "x_a"
                                                         FStar_Pervasives_Native.None
                                                         uu___20 in
                                                     let res =
                                                       let wp =
                                                         let uu___20 =
                                                           let uu___21 =
                                                             FStarC_TypeChecker_Env.inst_tscheme
                                                               ret_wp in
                                                           FStar_Pervasives_Native.snd
                                                             uu___21 in
                                                         let uu___21 =
                                                           let uu___22 =
                                                             let uu___23 =
                                                               FStarC_Syntax_Syntax.bv_to_name
                                                                 a in
                                                             FStarC_Syntax_Syntax.as_arg
                                                               uu___23 in
                                                           let uu___23 =
                                                             let uu___24 =
                                                               let uu___25 =
                                                                 FStarC_Syntax_Syntax.bv_to_name
                                                                   x_a in
                                                               FStarC_Syntax_Syntax.as_arg
                                                                 uu___25 in
                                                             [uu___24] in
                                                           uu___22 :: uu___23 in
                                                         FStarC_Syntax_Syntax.mk_Tm_app
                                                           uu___20 uu___21
                                                           FStarC_Compiler_Range_Type.dummyRange in
                                                       mk_repr a wp in
                                                     let k =
                                                       let uu___20 =
                                                         let uu___21 =
                                                           FStarC_Syntax_Syntax.mk_binder
                                                             a in
                                                         let uu___22 =
                                                           let uu___23 =
                                                             FStarC_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu___23] in
                                                         uu___21 :: uu___22 in
                                                       let uu___21 =
                                                         FStarC_Syntax_Syntax.mk_Total
                                                           res in
                                                       FStarC_Syntax_Util.arrow
                                                         uu___20 uu___21 in
                                                     let uu___20 =
                                                       FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env k in
                                                     (match uu___20 with
                                                      | (k1, uu___21,
                                                         uu___22) ->
                                                          let env1 =
                                                            let uu___23 =
                                                              FStarC_TypeChecker_Env.set_range
                                                                env
                                                                (FStar_Pervasives_Native.snd
                                                                   return_repr_ts).FStarC_Syntax_Syntax.pos in
                                                            FStar_Pervasives_Native.Some
                                                              uu___23 in
                                                          check_and_gen'
                                                            "return_repr"
                                                            Prims.int_one
                                                            env1
                                                            return_repr_ts
                                                            (FStar_Pervasives_Native.Some
                                                               k1)) in
                                               log_combinator "return_repr"
                                                 return_repr;
                                               (let bind_repr =
                                                  let bind_repr_ts =
                                                    let uu___19 =
                                                      FStarC_Syntax_Util.get_bind_repr
                                                        ed2 in
                                                    FStarC_Compiler_Util.must
                                                      uu___19 in
                                                  let uu___19 =
                                                    fresh_a_and_wp () in
                                                  match uu___19 with
                                                  | (a, wp_sort_a) ->
                                                      let uu___20 =
                                                        fresh_a_and_wp () in
                                                      (match uu___20 with
                                                       | (b, wp_sort_b) ->
                                                           let wp_sort_a_b =
                                                             let uu___21 =
                                                               let uu___22 =
                                                                 let uu___23
                                                                   =
                                                                   FStarC_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                 FStarC_Syntax_Syntax.null_binder
                                                                   uu___23 in
                                                               [uu___22] in
                                                             let uu___22 =
                                                               FStarC_Syntax_Syntax.mk_Total
                                                                 wp_sort_b in
                                                             FStarC_Syntax_Util.arrow
                                                               uu___21
                                                               uu___22 in
                                                           let wp_f =
                                                             FStarC_Syntax_Syntax.gen_bv
                                                               "wp_f"
                                                               FStar_Pervasives_Native.None
                                                               wp_sort_a in
                                                           let wp_g =
                                                             FStarC_Syntax_Syntax.gen_bv
                                                               "wp_g"
                                                               FStar_Pervasives_Native.None
                                                               wp_sort_a_b in
                                                           let x_a =
                                                             let uu___21 =
                                                               FStarC_Syntax_Syntax.bv_to_name
                                                                 a in
                                                             FStarC_Syntax_Syntax.gen_bv
                                                               "x_a"
                                                               FStar_Pervasives_Native.None
                                                               uu___21 in
                                                           let wp_g_x =
                                                             let uu___21 =
                                                               FStarC_Syntax_Syntax.bv_to_name
                                                                 wp_g in
                                                             let uu___22 =
                                                               let uu___23 =
                                                                 let uu___24
                                                                   =
                                                                   FStarC_Syntax_Syntax.bv_to_name
                                                                    x_a in
                                                                 FStarC_Syntax_Syntax.as_arg
                                                                   uu___24 in
                                                               [uu___23] in
                                                             FStarC_Syntax_Syntax.mk_Tm_app
                                                               uu___21
                                                               uu___22
                                                               FStarC_Compiler_Range_Type.dummyRange in
                                                           let res =
                                                             let wp =
                                                               let uu___21 =
                                                                 let uu___22
                                                                   =
                                                                   FStarC_TypeChecker_Env.inst_tscheme
                                                                    bind_wp in
                                                                 FStar_Pervasives_Native.snd
                                                                   uu___22 in
                                                               let uu___22 =
                                                                 let uu___23
                                                                   =
                                                                   let uu___24
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                   let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    wp_g in
                                                                    [uu___30] in
                                                                    uu___28
                                                                    ::
                                                                    uu___29 in
                                                                    uu___26
                                                                    ::
                                                                    uu___27 in
                                                                   uu___24 ::
                                                                    uu___25 in
                                                                 FStarC_Compiler_List.map
                                                                   FStarC_Syntax_Syntax.as_arg
                                                                   uu___23 in
                                                               FStarC_Syntax_Syntax.mk_Tm_app
                                                                 uu___21
                                                                 uu___22
                                                                 FStarC_Compiler_Range_Type.dummyRange in
                                                             mk_repr b wp in
                                                           let maybe_range_arg
                                                             =
                                                             let uu___21 =
                                                               FStarC_Compiler_Util.for_some
                                                                 (FStarC_TypeChecker_TermEqAndSimplify.eq_tm_bool
                                                                    env
                                                                    FStarC_Syntax_Util.dm4f_bind_range_attr)
                                                                 ed2.FStarC_Syntax_Syntax.eff_attrs in
                                                             if uu___21
                                                             then
                                                               let uu___22 =
                                                                 FStarC_Syntax_Syntax.null_binder
                                                                   FStarC_Syntax_Syntax.t_range in
                                                               let uu___23 =
                                                                 let uu___24
                                                                   =
                                                                   FStarC_Syntax_Syntax.null_binder
                                                                    FStarC_Syntax_Syntax.t_range in
                                                                 [uu___24] in
                                                               uu___22 ::
                                                                 uu___23
                                                             else [] in
                                                           let k =
                                                             let uu___21 =
                                                               let uu___22 =
                                                                 let uu___23
                                                                   =
                                                                   FStarC_Syntax_Syntax.mk_binder
                                                                    a in
                                                                 let uu___24
                                                                   =
                                                                   let uu___25
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_binder
                                                                    b in
                                                                   [uu___25] in
                                                                 uu___23 ::
                                                                   uu___24 in
                                                               let uu___23 =
                                                                 let uu___24
                                                                   =
                                                                   let uu___25
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_binder
                                                                    wp_f in
                                                                   let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    mk_repr a
                                                                    uu___29 in
                                                                    FStarC_Syntax_Syntax.null_binder
                                                                    uu___28 in
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_binder
                                                                    wp_g in
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                    [uu___34] in
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x in
                                                                    FStarC_Syntax_Syntax.mk_Total
                                                                    uu___35 in
                                                                    FStarC_Syntax_Util.arrow
                                                                    uu___33
                                                                    uu___34 in
                                                                    FStarC_Syntax_Syntax.null_binder
                                                                    uu___32 in
                                                                    [uu___31] in
                                                                    uu___29
                                                                    ::
                                                                    uu___30 in
                                                                    uu___27
                                                                    ::
                                                                    uu___28 in
                                                                   uu___25 ::
                                                                    uu___26 in
                                                                 FStarC_Compiler_List.op_At
                                                                   maybe_range_arg
                                                                   uu___24 in
                                                               FStarC_Compiler_List.op_At
                                                                 uu___22
                                                                 uu___23 in
                                                             let uu___22 =
                                                               FStarC_Syntax_Syntax.mk_Total
                                                                 res in
                                                             FStarC_Syntax_Util.arrow
                                                               uu___21
                                                               uu___22 in
                                                           let uu___21 =
                                                             FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                               env k in
                                                           (match uu___21
                                                            with
                                                            | (k1, uu___22,
                                                               uu___23) ->
                                                                let env1 =
                                                                  FStarC_TypeChecker_Env.set_range
                                                                    env
                                                                    (FStar_Pervasives_Native.snd
                                                                    bind_repr_ts).FStarC_Syntax_Syntax.pos in
                                                                let env2 =
                                                                  FStar_Pervasives_Native.Some
                                                                    {
                                                                    FStarC_TypeChecker_Env.solver
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.solver);
                                                                    FStarC_TypeChecker_Env.range
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.range);
                                                                    FStarC_TypeChecker_Env.curmodule
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.curmodule);
                                                                    FStarC_TypeChecker_Env.gamma
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.gamma);
                                                                    FStarC_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.gamma_sig);
                                                                    FStarC_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.gamma_cache);
                                                                    FStarC_TypeChecker_Env.modules
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.modules);
                                                                    FStarC_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.expected_typ);
                                                                    FStarC_TypeChecker_Env.sigtab
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.sigtab);
                                                                    FStarC_TypeChecker_Env.attrtab
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.attrtab);
                                                                    FStarC_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.instantiate_imp);
                                                                    FStarC_TypeChecker_Env.effects
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.effects);
                                                                    FStarC_TypeChecker_Env.generalize
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.generalize);
                                                                    FStarC_TypeChecker_Env.letrecs
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.letrecs);
                                                                    FStarC_TypeChecker_Env.top_level
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.top_level);
                                                                    FStarC_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.check_uvars);
                                                                    FStarC_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.use_eq_strict);
                                                                    FStarC_TypeChecker_Env.is_iface
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.is_iface);
                                                                    FStarC_TypeChecker_Env.admit
                                                                    = true;
                                                                    FStarC_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.lax_universes);
                                                                    FStarC_TypeChecker_Env.phase1
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.phase1);
                                                                    FStarC_TypeChecker_Env.failhard
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.failhard);
                                                                    FStarC_TypeChecker_Env.flychecking
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.flychecking);
                                                                    FStarC_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                                                                    FStarC_TypeChecker_Env.intactics
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.intactics);
                                                                    FStarC_TypeChecker_Env.nocoerce
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.nocoerce);
                                                                    FStarC_TypeChecker_Env.tc_term
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.tc_term);
                                                                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                                                    FStarC_TypeChecker_Env.universe_of
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.universe_of);
                                                                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                                                    FStarC_TypeChecker_Env.teq_nosmt_force
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                                                                    FStarC_TypeChecker_Env.subtype_nosmt_force
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                                                    FStarC_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStarC_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                                                                    FStarC_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                                                                    FStarC_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.proof_ns);
                                                                    FStarC_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.synth_hook);
                                                                    FStarC_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStarC_TypeChecker_Env.splice
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.splice);
                                                                    FStarC_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.mpreprocess);
                                                                    FStarC_TypeChecker_Env.postprocess
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.postprocess);
                                                                    FStarC_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.identifier_info);
                                                                    FStarC_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.tc_hooks);
                                                                    FStarC_TypeChecker_Env.dsenv
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.dsenv);
                                                                    FStarC_TypeChecker_Env.nbe
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.nbe);
                                                                    FStarC_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.strict_args_tab);
                                                                    FStarC_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                                                                    FStarC_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                                                    FStarC_TypeChecker_Env.unif_allow_ref_guards
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                                                    FStarC_TypeChecker_Env.erase_erasable_args
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                                                                    FStarC_TypeChecker_Env.core_check
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.core_check);
                                                                    FStarC_TypeChecker_Env.missing_decl
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.missing_decl)
                                                                    } in
                                                                check_and_gen'
                                                                  "bind_repr"
                                                                  (Prims.of_int (2))
                                                                  env2
                                                                  bind_repr_ts
                                                                  (FStar_Pervasives_Native.Some
                                                                    k1))) in
                                                log_combinator "bind_repr"
                                                  bind_repr;
                                                (let actions =
                                                   let check_action act =
                                                     if
                                                       (FStarC_Compiler_List.length
                                                          act.FStarC_Syntax_Syntax.action_params)
                                                         <> Prims.int_zero
                                                     then
                                                       failwith
                                                         "tc_eff_decl: expected action_params to be empty"
                                                     else ();
                                                     (let uu___21 =
                                                        if
                                                          act.FStarC_Syntax_Syntax.action_univs
                                                            = []
                                                        then (env, act)
                                                        else
                                                          (let uu___23 =
                                                             FStarC_Syntax_Subst.univ_var_opening
                                                               act.FStarC_Syntax_Syntax.action_univs in
                                                           match uu___23 with
                                                           | (usubst, uvs) ->
                                                               let uu___24 =
                                                                 FStarC_TypeChecker_Env.push_univ_vars
                                                                   env uvs in
                                                               let uu___25 =
                                                                 let uu___26
                                                                   =
                                                                   FStarC_Syntax_Subst.subst
                                                                    usubst
                                                                    act.FStarC_Syntax_Syntax.action_defn in
                                                                 let uu___27
                                                                   =
                                                                   FStarC_Syntax_Subst.subst
                                                                    usubst
                                                                    act.FStarC_Syntax_Syntax.action_typ in
                                                                 {
                                                                   FStarC_Syntax_Syntax.action_name
                                                                    =
                                                                    (act.FStarC_Syntax_Syntax.action_name);
                                                                   FStarC_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (act.FStarC_Syntax_Syntax.action_unqualified_name);
                                                                   FStarC_Syntax_Syntax.action_univs
                                                                    = uvs;
                                                                   FStarC_Syntax_Syntax.action_params
                                                                    =
                                                                    (act.FStarC_Syntax_Syntax.action_params);
                                                                   FStarC_Syntax_Syntax.action_defn
                                                                    = uu___26;
                                                                   FStarC_Syntax_Syntax.action_typ
                                                                    = uu___27
                                                                 } in
                                                               (uu___24,
                                                                 uu___25)) in
                                                      match uu___21 with
                                                      | (env1, act1) ->
                                                          let act_typ =
                                                            let uu___22 =
                                                              let uu___23 =
                                                                FStarC_Syntax_Subst.compress
                                                                  act1.FStarC_Syntax_Syntax.action_typ in
                                                              uu___23.FStarC_Syntax_Syntax.n in
                                                            match uu___22
                                                            with
                                                            | FStarC_Syntax_Syntax.Tm_arrow
                                                                {
                                                                  FStarC_Syntax_Syntax.bs1
                                                                    = bs1;
                                                                  FStarC_Syntax_Syntax.comp
                                                                    = c;_}
                                                                ->
                                                                let c1 =
                                                                  FStarC_TypeChecker_Env.comp_to_comp_typ
                                                                    env1 c in
                                                                let uu___23 =
                                                                  FStarC_Ident.lid_equals
                                                                    c1.FStarC_Syntax_Syntax.effect_name
                                                                    ed2.FStarC_Syntax_Syntax.mname in
                                                                if uu___23
                                                                then
                                                                  let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Compiler_List.hd
                                                                    c1.FStarC_Syntax_Syntax.effect_args in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___27 in
                                                                    mk_repr'
                                                                    c1.FStarC_Syntax_Syntax.result_typ
                                                                    uu___26 in
                                                                    FStarC_Syntax_Syntax.mk_Total
                                                                    uu___25 in
                                                                  FStarC_Syntax_Util.arrow
                                                                    bs1
                                                                    uu___24
                                                                else
                                                                  act1.FStarC_Syntax_Syntax.action_typ
                                                            | uu___23 ->
                                                                act1.FStarC_Syntax_Syntax.action_typ in
                                                          let uu___22 =
                                                            FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 act_typ in
                                                          (match uu___22 with
                                                           | (act_typ1,
                                                              uu___23, g_t)
                                                               ->
                                                               let env' =
                                                                 let uu___24
                                                                   =
                                                                   FStarC_TypeChecker_Env.set_expected_typ
                                                                    env1
                                                                    act_typ1 in
                                                                 {
                                                                   FStarC_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.solver);
                                                                   FStarC_TypeChecker_Env.range
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.range);
                                                                   FStarC_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.curmodule);
                                                                   FStarC_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.gamma);
                                                                   FStarC_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.gamma_sig);
                                                                   FStarC_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.gamma_cache);
                                                                   FStarC_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.modules);
                                                                   FStarC_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.expected_typ);
                                                                   FStarC_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.sigtab);
                                                                   FStarC_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.attrtab);
                                                                   FStarC_TypeChecker_Env.instantiate_imp
                                                                    = false;
                                                                   FStarC_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.effects);
                                                                   FStarC_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.generalize);
                                                                   FStarC_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.letrecs);
                                                                   FStarC_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.top_level);
                                                                   FStarC_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.check_uvars);
                                                                   FStarC_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.use_eq_strict);
                                                                   FStarC_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.is_iface);
                                                                   FStarC_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.admit);
                                                                   FStarC_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.lax_universes);
                                                                   FStarC_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.phase1);
                                                                   FStarC_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.failhard);
                                                                   FStarC_TypeChecker_Env.flychecking
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.flychecking);
                                                                   FStarC_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.uvar_subtyping);
                                                                   FStarC_TypeChecker_Env.intactics
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.intactics);
                                                                   FStarC_TypeChecker_Env.nocoerce
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.nocoerce);
                                                                   FStarC_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.tc_term);
                                                                   FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                                                   FStarC_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.universe_of);
                                                                   FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                                                   FStarC_TypeChecker_Env.teq_nosmt_force
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.teq_nosmt_force);
                                                                   FStarC_TypeChecker_Env.subtype_nosmt_force
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                                                   FStarC_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                                                   FStarC_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.normalized_eff_names);
                                                                   FStarC_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.fv_delta_depths);
                                                                   FStarC_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.proof_ns);
                                                                   FStarC_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.synth_hook);
                                                                   FStarC_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                                                   FStarC_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.splice);
                                                                   FStarC_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.mpreprocess);
                                                                   FStarC_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.postprocess);
                                                                   FStarC_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.identifier_info);
                                                                   FStarC_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.tc_hooks);
                                                                   FStarC_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.dsenv);
                                                                   FStarC_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.nbe);
                                                                   FStarC_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.strict_args_tab);
                                                                   FStarC_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.erasable_types_tab);
                                                                   FStarC_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                                                   FStarC_TypeChecker_Env.unif_allow_ref_guards
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                                                   FStarC_TypeChecker_Env.erase_erasable_args
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.erase_erasable_args);
                                                                   FStarC_TypeChecker_Env.core_check
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.core_check);
                                                                   FStarC_TypeChecker_Env.missing_decl
                                                                    =
                                                                    (uu___24.FStarC_TypeChecker_Env.missing_decl)
                                                                 } in
                                                               ((let uu___25
                                                                   =
                                                                   FStarC_Compiler_Effect.op_Bang
                                                                    dbg in
                                                                 if uu___25
                                                                 then
                                                                   let uu___26
                                                                    =
                                                                    FStarC_Ident.string_of_lid
                                                                    act1.FStarC_Syntax_Syntax.action_name in
                                                                   let uu___27
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    act1.FStarC_Syntax_Syntax.action_defn in
                                                                   let uu___28
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    act_typ1 in
                                                                   FStarC_Compiler_Util.print3
                                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                                    uu___26
                                                                    uu___27
                                                                    uu___28
                                                                 else ());
                                                                (let uu___25
                                                                   =
                                                                   FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env'
                                                                    act1.FStarC_Syntax_Syntax.action_defn in
                                                                 match uu___25
                                                                 with
                                                                 | (act_defn,
                                                                    uu___26,
                                                                    g_a) ->
                                                                    ((
                                                                    let uu___28
                                                                    =
                                                                    FStarC_TypeChecker_Env.conj_guards
                                                                    [g_a;
                                                                    g_t] in
                                                                    FStarC_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu___28);
                                                                    (let act_defn1
                                                                    =
                                                                    FStarC_TypeChecker_Normalize.normalize
                                                                    [
                                                                    FStarC_TypeChecker_Env.UnfoldUntil
                                                                    FStarC_Syntax_Syntax.delta_constant]
                                                                    env1
                                                                    act_defn in
                                                                    let act_typ2
                                                                    =
                                                                    FStarC_TypeChecker_Normalize.normalize
                                                                    [
                                                                    FStarC_TypeChecker_Env.UnfoldUntil
                                                                    FStarC_Syntax_Syntax.delta_constant;
                                                                    FStarC_TypeChecker_Env.Eager_unfolding;
                                                                    FStarC_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ1 in
                                                                    let uu___28
                                                                    =
                                                                    let act_typ3
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    act_typ2 in
                                                                    match 
                                                                    act_typ3.FStarC_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_arrow
                                                                    {
                                                                    FStarC_Syntax_Syntax.bs1
                                                                    = bs1;
                                                                    FStarC_Syntax_Syntax.comp
                                                                    = c;_} ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu___29
                                                                    with
                                                                    | 
                                                                    (bs2,
                                                                    uu___30)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStarC_Syntax_Syntax.tun
                                                                    FStarC_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu___31
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStarC_Syntax_Util.arrow
                                                                    bs2
                                                                    uu___31 in
                                                                    let uu___31
                                                                    =
                                                                    FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k in
                                                                    (match uu___31
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu___32,
                                                                    g) ->
                                                                    (k1, g)))
                                                                    | 
                                                                    uu___29
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    act_typ3 in
                                                                    let uu___32
                                                                    =
                                                                    FStarC_Class_Tagged.tag_of
                                                                    FStarC_Syntax_Syntax.tagged_term
                                                                    act_typ3 in
                                                                    FStarC_Compiler_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu___31
                                                                    uu___32 in
                                                                    FStarC_Errors.raise_error
                                                                    (FStarC_Syntax_Syntax.has_range_syntax
                                                                    ())
                                                                    act_defn1
                                                                    FStarC_Errors_Codes.Fatal_ActionMustHaveFunctionType
                                                                    ()
                                                                    (Obj.magic
                                                                    FStarC_Errors_Msg.is_error_message_string)
                                                                    (Obj.magic
                                                                    uu___30) in
                                                                    match uu___28
                                                                    with
                                                                    | 
                                                                    (expected_k,
                                                                    g_k) ->
                                                                    ((
                                                                    let g =
                                                                    FStarC_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k in
                                                                    let g1 =
                                                                    FStarC_TypeChecker_Env.conj_guard
                                                                    g g_k in
                                                                    match 
                                                                    g1.FStarC_TypeChecker_Common.guard_f
                                                                    with
                                                                    | 
                                                                    FStarC_TypeChecker_Common.NonTrivial
                                                                    uu___30
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    act_typ2 in
                                                                    FStarC_Compiler_Util.format1
                                                                    "Unexpected non trivial guard formula when checking action type shape (%s)"
                                                                    uu___32 in
                                                                    FStarC_Errors.raise_error
                                                                    (FStarC_Syntax_Syntax.has_range_syntax
                                                                    ())
                                                                    act_defn1
                                                                    FStarC_Errors_Codes.Fatal_ActionMustHaveFunctionType
                                                                    ()
                                                                    (Obj.magic
                                                                    FStarC_Errors_Msg.is_error_message_string)
                                                                    (Obj.magic
                                                                    uu___31)
                                                                    | 
                                                                    FStarC_TypeChecker_Common.Trivial
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_Env.conj_guards
                                                                    [g_k; g1] in
                                                                    FStarC_TypeChecker_Rel.force_trivial_guard
                                                                    {
                                                                    FStarC_TypeChecker_Env.solver
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.solver);
                                                                    FStarC_TypeChecker_Env.range
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.range);
                                                                    FStarC_TypeChecker_Env.curmodule
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.curmodule);
                                                                    FStarC_TypeChecker_Env.gamma
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.gamma);
                                                                    FStarC_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.gamma_sig);
                                                                    FStarC_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.gamma_cache);
                                                                    FStarC_TypeChecker_Env.modules
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.modules);
                                                                    FStarC_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.expected_typ);
                                                                    FStarC_TypeChecker_Env.sigtab
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.sigtab);
                                                                    FStarC_TypeChecker_Env.attrtab
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.attrtab);
                                                                    FStarC_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.instantiate_imp);
                                                                    FStarC_TypeChecker_Env.effects
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.effects);
                                                                    FStarC_TypeChecker_Env.generalize
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.generalize);
                                                                    FStarC_TypeChecker_Env.letrecs
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.letrecs);
                                                                    FStarC_TypeChecker_Env.top_level
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.top_level);
                                                                    FStarC_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.check_uvars);
                                                                    FStarC_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.use_eq_strict);
                                                                    FStarC_TypeChecker_Env.is_iface
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.is_iface);
                                                                    FStarC_TypeChecker_Env.admit
                                                                    = true;
                                                                    FStarC_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.lax_universes);
                                                                    FStarC_TypeChecker_Env.phase1
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.phase1);
                                                                    FStarC_TypeChecker_Env.failhard
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.failhard);
                                                                    FStarC_TypeChecker_Env.flychecking
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.flychecking);
                                                                    FStarC_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                                                                    FStarC_TypeChecker_Env.intactics
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.intactics);
                                                                    FStarC_TypeChecker_Env.nocoerce
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.nocoerce);
                                                                    FStarC_TypeChecker_Env.tc_term
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.tc_term);
                                                                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                                                    FStarC_TypeChecker_Env.universe_of
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.universe_of);
                                                                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                                                    FStarC_TypeChecker_Env.teq_nosmt_force
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                                                                    FStarC_TypeChecker_Env.subtype_nosmt_force
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                                                    FStarC_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStarC_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                                                                    FStarC_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                                                                    FStarC_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.proof_ns);
                                                                    FStarC_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.synth_hook);
                                                                    FStarC_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStarC_TypeChecker_Env.splice
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.splice);
                                                                    FStarC_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.mpreprocess);
                                                                    FStarC_TypeChecker_Env.postprocess
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.postprocess);
                                                                    FStarC_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.identifier_info);
                                                                    FStarC_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.tc_hooks);
                                                                    FStarC_TypeChecker_Env.dsenv
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.dsenv);
                                                                    FStarC_TypeChecker_Env.nbe
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.nbe);
                                                                    FStarC_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.strict_args_tab);
                                                                    FStarC_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                                                                    FStarC_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                                                    FStarC_TypeChecker_Env.unif_allow_ref_guards
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                                                    FStarC_TypeChecker_Env.erase_erasable_args
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                                                                    FStarC_TypeChecker_Env.core_check
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.core_check);
                                                                    FStarC_TypeChecker_Env.missing_decl
                                                                    =
                                                                    (env1.FStarC_TypeChecker_Env.missing_decl)
                                                                    } uu___30);
                                                                    (let act_typ3
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu___31.FStarC_Syntax_Syntax.n in
                                                                    match uu___30
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_arrow
                                                                    {
                                                                    FStarC_Syntax_Syntax.bs1
                                                                    = bs1;
                                                                    FStarC_Syntax_Syntax.comp
                                                                    = c;_} ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu___31
                                                                    with
                                                                    | 
                                                                    (bs2, c1)
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    destruct_repr
                                                                    (FStarC_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu___32
                                                                    with
                                                                    | 
                                                                    (a, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_Env.push_binders
                                                                    env1 bs2 in
                                                                    env1.FStarC_TypeChecker_Env.universe_of
                                                                    uu___35 a in
                                                                    [uu___34] in
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu___35] in
                                                                    {
                                                                    FStarC_Syntax_Syntax.comp_univs
                                                                    = uu___33;
                                                                    FStarC_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStarC_Syntax_Syntax.mname);
                                                                    FStarC_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStarC_Syntax_Syntax.effect_args
                                                                    = uu___34;
                                                                    FStarC_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu___33
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStarC_Syntax_Util.arrow
                                                                    bs2
                                                                    uu___33))
                                                                    | 
                                                                    uu___31
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                    let uu___30
                                                                    =
                                                                    if
                                                                    act1.FStarC_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStarC_TypeChecker_Generalize.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu___32
                                                                    =
                                                                    FStarC_Syntax_Subst.close_univ_vars
                                                                    act1.FStarC_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStarC_Syntax_Syntax.action_univs),
                                                                    uu___32)) in
                                                                    match uu___30
                                                                    with
                                                                    | 
                                                                    (univs,
                                                                    act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStarC_TypeChecker_Normalize.normalize
                                                                    [FStarC_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ3 in
                                                                    let act_typ5
                                                                    =
                                                                    FStarC_Syntax_Subst.close_univ_vars
                                                                    univs
                                                                    act_typ4 in
                                                                    {
                                                                    FStarC_Syntax_Syntax.action_name
                                                                    =
                                                                    (act1.FStarC_Syntax_Syntax.action_name);
                                                                    FStarC_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (act1.FStarC_Syntax_Syntax.action_unqualified_name);
                                                                    FStarC_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStarC_Syntax_Syntax.action_params
                                                                    =
                                                                    (act1.FStarC_Syntax_Syntax.action_params);
                                                                    FStarC_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStarC_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    })))))))) in
                                                   FStarC_Compiler_List.map
                                                     check_action
                                                     ed2.FStarC_Syntax_Syntax.actions in
                                                 ((FStar_Pervasives_Native.Some
                                                     repr),
                                                   (FStar_Pervasives_Native.Some
                                                      return_repr),
                                                   (FStar_Pervasives_Native.Some
                                                      bind_repr), actions))))) in
                                       match uu___14 with
                                       | (repr, return_repr, bind_repr,
                                          actions) ->
                                           let cl ts =
                                             let ts1 =
                                               FStarC_Syntax_Subst.close_tscheme
                                                 ed_bs ts in
                                             let ed_univs_closing =
                                               FStarC_Syntax_Subst.univ_var_closing
                                                 ed_univs in
                                             let uu___15 =
                                               FStarC_Syntax_Subst.shift_subst
                                                 (FStarC_Compiler_List.length
                                                    ed_bs) ed_univs_closing in
                                             FStarC_Syntax_Subst.subst_tscheme
                                               uu___15 ts1 in
                                           let combinators =
                                             {
                                               FStarC_Syntax_Syntax.ret_wp =
                                                 ret_wp;
                                               FStarC_Syntax_Syntax.bind_wp =
                                                 bind_wp;
                                               FStarC_Syntax_Syntax.stronger
                                                 = stronger;
                                               FStarC_Syntax_Syntax.if_then_else
                                                 = if_then_else;
                                               FStarC_Syntax_Syntax.ite_wp =
                                                 ite_wp;
                                               FStarC_Syntax_Syntax.close_wp
                                                 = close_wp;
                                               FStarC_Syntax_Syntax.trivial =
                                                 trivial;
                                               FStarC_Syntax_Syntax.repr =
                                                 repr;
                                               FStarC_Syntax_Syntax.return_repr
                                                 = return_repr;
                                               FStarC_Syntax_Syntax.bind_repr
                                                 = bind_repr
                                             } in
                                           let combinators1 =
                                             FStarC_Syntax_Util.apply_wp_eff_combinators
                                               cl combinators in
                                           let combinators2 =
                                             match ed2.FStarC_Syntax_Syntax.combinators
                                             with
                                             | FStarC_Syntax_Syntax.Primitive_eff
                                                 uu___15 ->
                                                 FStarC_Syntax_Syntax.Primitive_eff
                                                   combinators1
                                             | FStarC_Syntax_Syntax.DM4F_eff
                                                 uu___15 ->
                                                 FStarC_Syntax_Syntax.DM4F_eff
                                                   combinators1
                                             | uu___15 ->
                                                 failwith
                                                   "Impossible! tc_eff_decl on a layered effect is not expected" in
                                           let ed3 =
                                             let uu___15 =
                                               let uu___16 = cl signature in
                                               FStarC_Syntax_Syntax.WP_eff_sig
                                                 uu___16 in
                                             let uu___16 =
                                               FStarC_Compiler_List.map
                                                 (fun a ->
                                                    let uu___17 =
                                                      let uu___18 =
                                                        cl
                                                          ((a.FStarC_Syntax_Syntax.action_univs),
                                                            (a.FStarC_Syntax_Syntax.action_defn)) in
                                                      FStar_Pervasives_Native.snd
                                                        uu___18 in
                                                    let uu___18 =
                                                      let uu___19 =
                                                        cl
                                                          ((a.FStarC_Syntax_Syntax.action_univs),
                                                            (a.FStarC_Syntax_Syntax.action_typ)) in
                                                      FStar_Pervasives_Native.snd
                                                        uu___19 in
                                                    {
                                                      FStarC_Syntax_Syntax.action_name
                                                        =
                                                        (a.FStarC_Syntax_Syntax.action_name);
                                                      FStarC_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (a.FStarC_Syntax_Syntax.action_unqualified_name);
                                                      FStarC_Syntax_Syntax.action_univs
                                                        =
                                                        (a.FStarC_Syntax_Syntax.action_univs);
                                                      FStarC_Syntax_Syntax.action_params
                                                        =
                                                        (a.FStarC_Syntax_Syntax.action_params);
                                                      FStarC_Syntax_Syntax.action_defn
                                                        = uu___17;
                                                      FStarC_Syntax_Syntax.action_typ
                                                        = uu___18
                                                    }) actions in
                                             {
                                               FStarC_Syntax_Syntax.mname =
                                                 (ed2.FStarC_Syntax_Syntax.mname);
                                               FStarC_Syntax_Syntax.cattributes
                                                 =
                                                 (ed2.FStarC_Syntax_Syntax.cattributes);
                                               FStarC_Syntax_Syntax.univs =
                                                 (ed2.FStarC_Syntax_Syntax.univs);
                                               FStarC_Syntax_Syntax.binders =
                                                 (ed2.FStarC_Syntax_Syntax.binders);
                                               FStarC_Syntax_Syntax.signature
                                                 = uu___15;
                                               FStarC_Syntax_Syntax.combinators
                                                 = combinators2;
                                               FStarC_Syntax_Syntax.actions =
                                                 uu___16;
                                               FStarC_Syntax_Syntax.eff_attrs
                                                 =
                                                 (ed2.FStarC_Syntax_Syntax.eff_attrs);
                                               FStarC_Syntax_Syntax.extraction_mode
                                                 =
                                                 (ed2.FStarC_Syntax_Syntax.extraction_mode)
                                             } in
                                           ((let uu___16 =
                                               FStarC_Compiler_Effect.op_Bang
                                                 dbg in
                                             if uu___16
                                             then
                                               let uu___17 =
                                                 FStarC_Class_Show.show
                                                   FStarC_Syntax_Print.showable_eff_decl
                                                   ed3 in
                                               FStarC_Compiler_Util.print1
                                                 "Typechecked effect declaration:\n\t%s\n"
                                                 uu___17
                                             else ());
                                            ed3))))))))))))))
let (tc_eff_decl :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.eff_decl ->
      FStarC_Syntax_Syntax.qualifier Prims.list ->
        FStarC_Syntax_Syntax.attribute Prims.list ->
          FStarC_Syntax_Syntax.eff_decl)
  =
  fun env ->
    fun ed ->
      fun quals ->
        fun attrs ->
          let uu___ = FStarC_Syntax_Util.is_layered ed in
          if uu___
          then tc_layered_eff_decl env ed quals attrs
          else tc_non_layered_eff_decl env ed quals attrs
let (monad_signature :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Syntax_Syntax.term ->
        (FStarC_Syntax_Syntax.bv * FStarC_Syntax_Syntax.term'
          FStarC_Syntax_Syntax.syntax))
  =
  fun env ->
    fun m ->
      fun s ->
        let fail uu___ =
          let uu___1 = FStarC_Ident.range_of_lid m in
          FStarC_TypeChecker_Err.unexpected_signature_for_monad env uu___1 m
            s in
        let s1 = FStarC_Syntax_Subst.compress s in
        match s1.FStarC_Syntax_Syntax.n with
        | FStarC_Syntax_Syntax.Tm_arrow
            { FStarC_Syntax_Syntax.bs1 = bs; FStarC_Syntax_Syntax.comp = c;_}
            ->
            let bs1 = FStarC_Syntax_Subst.open_binders bs in
            (match bs1 with
             | { FStarC_Syntax_Syntax.binder_bv = a;
                 FStarC_Syntax_Syntax.binder_qual = uu___;
                 FStarC_Syntax_Syntax.binder_positivity = uu___1;
                 FStarC_Syntax_Syntax.binder_attrs = uu___2;_}::{
                                                                  FStarC_Syntax_Syntax.binder_bv
                                                                    = wp;
                                                                  FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___3;
                                                                  FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___4;
                                                                  FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___5;_}::[]
                 -> (a, (wp.FStarC_Syntax_Syntax.sort))
             | uu___ -> fail ())
        | uu___ -> fail ()
let (tc_layered_lift :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.sub_eff -> FStarC_Syntax_Syntax.sub_eff)
  =
  fun env0 ->
    fun sub ->
      (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_LayeredEffectsTc in
       if uu___1
       then
         let uu___2 =
           FStarC_Class_Show.show FStarC_Syntax_Print.showable_sub_eff sub in
         FStarC_Compiler_Util.print1 "Typechecking sub_effect: %s\n" uu___2
       else ());
      (let lift_ts = FStarC_Compiler_Util.must sub.FStarC_Syntax_Syntax.lift in
       let r = (FStar_Pervasives_Native.snd lift_ts).FStarC_Syntax_Syntax.pos in
       let uu___1 = check_and_gen env0 "" "lift" Prims.int_one lift_ts in
       match uu___1 with
       | (us, lift, lift_ty) ->
           ((let uu___3 = FStarC_Compiler_Effect.op_Bang dbg_LayeredEffectsTc in
             if uu___3
             then
               let uu___4 = FStarC_Syntax_Print.tscheme_to_string (us, lift) in
               let uu___5 =
                 FStarC_Syntax_Print.tscheme_to_string (us, lift_ty) in
               FStarC_Compiler_Util.print2
                 "Typechecked lift: %s and lift_ty: %s\n" uu___4 uu___5
             else ());
            (let uu___3 = FStarC_Syntax_Subst.open_univ_vars us lift_ty in
             match uu___3 with
             | (us1, lift_ty1) ->
                 let env = FStarC_TypeChecker_Env.push_univ_vars env0 us1 in
                 let uu___4 =
                   let uu___5 = FStarC_Compiler_List.hd us1 in
                   validate_indexed_effect_lift_shape env
                     sub.FStarC_Syntax_Syntax.source
                     sub.FStarC_Syntax_Syntax.target uu___5 lift_ty1 r in
                 (match uu___4 with
                  | (k, kind) ->
                      let sub1 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              FStarC_Syntax_Subst.close_univ_vars us1 k in
                            (us1, uu___7) in
                          FStar_Pervasives_Native.Some uu___6 in
                        {
                          FStarC_Syntax_Syntax.source =
                            (sub.FStarC_Syntax_Syntax.source);
                          FStarC_Syntax_Syntax.target =
                            (sub.FStarC_Syntax_Syntax.target);
                          FStarC_Syntax_Syntax.lift_wp = uu___5;
                          FStarC_Syntax_Syntax.lift =
                            (FStar_Pervasives_Native.Some (us1, lift));
                          FStarC_Syntax_Syntax.kind =
                            (FStar_Pervasives_Native.Some kind)
                        } in
                      ((let uu___6 =
                          FStarC_Compiler_Effect.op_Bang dbg_LayeredEffectsTc in
                        if uu___6
                        then
                          let uu___7 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_sub_eff sub1 in
                          FStarC_Compiler_Util.print1
                            "Final sub_effect: %s\n" uu___7
                        else ());
                       sub1)))))
let (check_lift_for_erasable_effects :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Ident.lident -> FStarC_Compiler_Range_Type.range -> unit)
  =
  fun env ->
    fun m1 ->
      fun m2 ->
        fun r ->
          let err reason =
            let uu___ =
              let uu___1 = FStarC_Ident.string_of_lid m1 in
              let uu___2 = FStarC_Ident.string_of_lid m2 in
              FStarC_Compiler_Util.format3
                "Error defining a lift/subcomp %s ~> %s: %s" uu___1 uu___2
                reason in
            FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
              FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___) in
          let m11 = FStarC_TypeChecker_Env.norm_eff_name env m1 in
          let uu___ =
            FStarC_Ident.lid_equals m11 FStarC_Parser_Const.effect_GHOST_lid in
          if uu___
          then err "user-defined lifts from GHOST effect are not allowed"
          else
            (let m1_erasable =
               FStarC_TypeChecker_Env.is_erasable_effect env m11 in
             let m2_erasable =
               FStarC_TypeChecker_Env.is_erasable_effect env m2 in
             let uu___2 =
               (m2_erasable && (Prims.op_Negation m1_erasable)) &&
                 (let uu___3 =
                    FStarC_Ident.lid_equals m11
                      FStarC_Parser_Const.effect_PURE_lid in
                  Prims.op_Negation uu___3) in
             if uu___2
             then
               err
                 "cannot lift a non-erasable effect to an erasable effect unless the non-erasable effect is PURE"
             else ())
let (tc_lift :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.sub_eff ->
      FStarC_Compiler_Range_Type.range -> FStarC_Syntax_Syntax.sub_eff)
  =
  fun env ->
    fun sub ->
      fun r ->
        (let uu___1 =
           FStarC_Ident.lid_equals sub.FStarC_Syntax_Syntax.source
             sub.FStarC_Syntax_Syntax.target in
         if uu___1
         then
           let uu___2 =
             let uu___3 =
               FStarC_Class_Show.show FStarC_Ident.showable_lident
                 sub.FStarC_Syntax_Syntax.source in
             FStarC_Compiler_Util.format1
               "Cannot define a lift with same source and target (%s)" uu___3 in
           FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
             FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_string)
             (Obj.magic uu___2)
         else ());
        (let check_and_gen1 env1 t k =
           let uu___1 =
             FStarC_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k in
           FStarC_TypeChecker_Generalize.generalize_universes env1 uu___1 in
         check_lift_for_erasable_effects env sub.FStarC_Syntax_Syntax.source
           sub.FStarC_Syntax_Syntax.target r;
         (let ed_src =
            FStarC_TypeChecker_Env.get_effect_decl env
              sub.FStarC_Syntax_Syntax.source in
          let ed_tgt =
            FStarC_TypeChecker_Env.get_effect_decl env
              sub.FStarC_Syntax_Syntax.target in
          let uu___2 =
            (FStarC_Syntax_Util.is_layered ed_src) ||
              (FStarC_Syntax_Util.is_layered ed_tgt) in
          if uu___2
          then
            let uu___3 = FStarC_TypeChecker_Env.set_range env r in
            tc_layered_lift uu___3 sub
          else
            (let uu___4 =
               let uu___5 =
                 FStarC_TypeChecker_Env.lookup_effect_lid env
                   sub.FStarC_Syntax_Syntax.source in
               monad_signature env sub.FStarC_Syntax_Syntax.source uu___5 in
             match uu___4 with
             | (a, wp_a_src) ->
                 let uu___5 =
                   let uu___6 =
                     FStarC_TypeChecker_Env.lookup_effect_lid env
                       sub.FStarC_Syntax_Syntax.target in
                   monad_signature env sub.FStarC_Syntax_Syntax.target uu___6 in
                 (match uu___5 with
                  | (b, wp_b_tgt) ->
                      let wp_a_tgt =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 = FStarC_Syntax_Syntax.bv_to_name a in
                              (b, uu___9) in
                            FStarC_Syntax_Syntax.NT uu___8 in
                          [uu___7] in
                        FStarC_Syntax_Subst.subst uu___6 wp_b_tgt in
                      let expected_k =
                        let uu___6 =
                          let uu___7 = FStarC_Syntax_Syntax.mk_binder a in
                          let uu___8 =
                            let uu___9 =
                              FStarC_Syntax_Syntax.null_binder wp_a_src in
                            [uu___9] in
                          uu___7 :: uu___8 in
                        let uu___7 = FStarC_Syntax_Syntax.mk_Total wp_a_tgt in
                        FStarC_Syntax_Util.arrow uu___6 uu___7 in
                      let repr_type eff_name a1 wp =
                        (let uu___7 =
                           let uu___8 =
                             FStarC_TypeChecker_Env.is_reifiable_effect env
                               eff_name in
                           Prims.op_Negation uu___8 in
                         if uu___7
                         then
                           let uu___8 =
                             let uu___9 = FStarC_Ident.string_of_lid eff_name in
                             FStarC_Compiler_Util.format1
                               "Effect %s cannot be reified" uu___9 in
                           FStarC_Errors.raise_error
                             FStarC_TypeChecker_Env.hasRange_env env
                             FStarC_Errors_Codes.Fatal_EffectCannotBeReified
                             ()
                             (Obj.magic
                                FStarC_Errors_Msg.is_error_message_string)
                             (Obj.magic uu___8)
                         else ());
                        (let uu___7 =
                           FStarC_TypeChecker_Env.effect_decl_opt env
                             eff_name in
                         match uu___7 with
                         | FStar_Pervasives_Native.None ->
                             failwith
                               "internal error: reifiable effect has no decl?"
                         | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                             let repr =
                               let uu___8 =
                                 let uu___9 =
                                   FStarC_Syntax_Util.get_eff_repr ed in
                                 FStarC_Compiler_Util.must uu___9 in
                               FStarC_TypeChecker_Env.inst_effect_fun_with
                                 [FStarC_Syntax_Syntax.U_unknown] env ed
                                 uu___8 in
                             let uu___8 =
                               let uu___9 =
                                 let uu___10 =
                                   let uu___11 =
                                     FStarC_Syntax_Syntax.as_arg a1 in
                                   let uu___12 =
                                     let uu___13 =
                                       FStarC_Syntax_Syntax.as_arg wp in
                                     [uu___13] in
                                   uu___11 :: uu___12 in
                                 {
                                   FStarC_Syntax_Syntax.hd = repr;
                                   FStarC_Syntax_Syntax.args = uu___10
                                 } in
                               FStarC_Syntax_Syntax.Tm_app uu___9 in
                             let uu___9 =
                               FStarC_TypeChecker_Env.get_range env in
                             FStarC_Syntax_Syntax.mk uu___8 uu___9) in
                      let uu___6 =
                        match ((sub.FStarC_Syntax_Syntax.lift),
                                (sub.FStarC_Syntax_Syntax.lift_wp))
                        with
                        | (FStar_Pervasives_Native.None,
                           FStar_Pervasives_Native.None) ->
                            failwith "Impossible (parser)"
                        | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                            ->
                            let uu___7 =
                              if
                                (FStarC_Compiler_List.length uvs) >
                                  Prims.int_zero
                              then
                                let uu___8 =
                                  FStarC_Syntax_Subst.univ_var_opening uvs in
                                match uu___8 with
                                | (usubst, uvs1) ->
                                    let uu___9 =
                                      FStarC_TypeChecker_Env.push_univ_vars
                                        env uvs1 in
                                    let uu___10 =
                                      FStarC_Syntax_Subst.subst usubst
                                        lift_wp in
                                    (uu___9, uu___10)
                              else (env, lift_wp) in
                            (match uu___7 with
                             | (env1, lift_wp1) ->
                                 let lift_wp2 =
                                   if
                                     (FStarC_Compiler_List.length uvs) =
                                       Prims.int_zero
                                   then
                                     check_and_gen1 env1 lift_wp1 expected_k
                                   else
                                     (let lift_wp3 =
                                        FStarC_TypeChecker_TcTerm.tc_check_trivial_guard
                                          env1 lift_wp1 expected_k in
                                      let uu___9 =
                                        FStarC_Syntax_Subst.close_univ_vars
                                          uvs lift_wp3 in
                                      (uvs, uu___9)) in
                                 (lift, lift_wp2))
                        | (FStar_Pervasives_Native.Some (what, lift),
                           FStar_Pervasives_Native.None) ->
                            let uu___7 =
                              if
                                (FStarC_Compiler_List.length what) >
                                  Prims.int_zero
                              then
                                let uu___8 =
                                  FStarC_Syntax_Subst.univ_var_opening what in
                                match uu___8 with
                                | (usubst, uvs) ->
                                    let uu___9 =
                                      FStarC_Syntax_Subst.subst usubst lift in
                                    (uvs, uu___9)
                              else ([], lift) in
                            (match uu___7 with
                             | (uvs, lift1) ->
                                 ((let uu___9 =
                                     FStarC_Compiler_Effect.op_Bang dbg in
                                   if uu___9
                                   then
                                     let uu___10 =
                                       FStarC_Class_Show.show
                                         FStarC_Syntax_Print.showable_term
                                         lift1 in
                                     FStarC_Compiler_Util.print1
                                       "Lift for free : %s\n" uu___10
                                   else ());
                                  (let dmff_env =
                                     FStarC_TypeChecker_DMFF.empty env
                                       (FStarC_TypeChecker_TcTerm.tc_constant
                                          env
                                          FStarC_Compiler_Range_Type.dummyRange) in
                                   let uu___9 =
                                     let uu___10 =
                                       FStarC_TypeChecker_Env.push_univ_vars
                                         env uvs in
                                     FStarC_TypeChecker_TcTerm.tc_term
                                       uu___10 lift1 in
                                   match uu___9 with
                                   | (lift2, comp, uu___10) ->
                                       let uu___11 =
                                         FStarC_TypeChecker_DMFF.star_expr
                                           dmff_env lift2 in
                                       (match uu___11 with
                                        | (uu___12, lift_wp, lift_elab) ->
                                            let lift_wp1 =
                                              FStarC_TypeChecker_DMFF.recheck_debug
                                                "lift-wp" env lift_wp in
                                            let lift_elab1 =
                                              FStarC_TypeChecker_DMFF.recheck_debug
                                                "lift-elab" env lift_elab in
                                            if
                                              (FStarC_Compiler_List.length
                                                 uvs)
                                                = Prims.int_zero
                                            then
                                              let uu___13 =
                                                let uu___14 =
                                                  FStarC_TypeChecker_Generalize.generalize_universes
                                                    env lift_elab1 in
                                                FStar_Pervasives_Native.Some
                                                  uu___14 in
                                              let uu___14 =
                                                FStarC_TypeChecker_Generalize.generalize_universes
                                                  env lift_wp1 in
                                              (uu___13, uu___14)
                                            else
                                              (let uu___14 =
                                                 let uu___15 =
                                                   let uu___16 =
                                                     FStarC_Syntax_Subst.close_univ_vars
                                                       uvs lift_elab1 in
                                                   (uvs, uu___16) in
                                                 FStar_Pervasives_Native.Some
                                                   uu___15 in
                                               let uu___15 =
                                                 let uu___16 =
                                                   FStarC_Syntax_Subst.close_univ_vars
                                                     uvs lift_wp1 in
                                                 (uvs, uu___16) in
                                               (uu___14, uu___15)))))) in
                      (match uu___6 with
                       | (lift, lift_wp) ->
                           let env1 =
                             {
                               FStarC_TypeChecker_Env.solver =
                                 (env.FStarC_TypeChecker_Env.solver);
                               FStarC_TypeChecker_Env.range =
                                 (env.FStarC_TypeChecker_Env.range);
                               FStarC_TypeChecker_Env.curmodule =
                                 (env.FStarC_TypeChecker_Env.curmodule);
                               FStarC_TypeChecker_Env.gamma =
                                 (env.FStarC_TypeChecker_Env.gamma);
                               FStarC_TypeChecker_Env.gamma_sig =
                                 (env.FStarC_TypeChecker_Env.gamma_sig);
                               FStarC_TypeChecker_Env.gamma_cache =
                                 (env.FStarC_TypeChecker_Env.gamma_cache);
                               FStarC_TypeChecker_Env.modules =
                                 (env.FStarC_TypeChecker_Env.modules);
                               FStarC_TypeChecker_Env.expected_typ =
                                 (env.FStarC_TypeChecker_Env.expected_typ);
                               FStarC_TypeChecker_Env.sigtab =
                                 (env.FStarC_TypeChecker_Env.sigtab);
                               FStarC_TypeChecker_Env.attrtab =
                                 (env.FStarC_TypeChecker_Env.attrtab);
                               FStarC_TypeChecker_Env.instantiate_imp =
                                 (env.FStarC_TypeChecker_Env.instantiate_imp);
                               FStarC_TypeChecker_Env.effects =
                                 (env.FStarC_TypeChecker_Env.effects);
                               FStarC_TypeChecker_Env.generalize =
                                 (env.FStarC_TypeChecker_Env.generalize);
                               FStarC_TypeChecker_Env.letrecs =
                                 (env.FStarC_TypeChecker_Env.letrecs);
                               FStarC_TypeChecker_Env.top_level =
                                 (env.FStarC_TypeChecker_Env.top_level);
                               FStarC_TypeChecker_Env.check_uvars =
                                 (env.FStarC_TypeChecker_Env.check_uvars);
                               FStarC_TypeChecker_Env.use_eq_strict =
                                 (env.FStarC_TypeChecker_Env.use_eq_strict);
                               FStarC_TypeChecker_Env.is_iface =
                                 (env.FStarC_TypeChecker_Env.is_iface);
                               FStarC_TypeChecker_Env.admit = true;
                               FStarC_TypeChecker_Env.lax_universes =
                                 (env.FStarC_TypeChecker_Env.lax_universes);
                               FStarC_TypeChecker_Env.phase1 =
                                 (env.FStarC_TypeChecker_Env.phase1);
                               FStarC_TypeChecker_Env.failhard =
                                 (env.FStarC_TypeChecker_Env.failhard);
                               FStarC_TypeChecker_Env.flychecking =
                                 (env.FStarC_TypeChecker_Env.flychecking);
                               FStarC_TypeChecker_Env.uvar_subtyping =
                                 (env.FStarC_TypeChecker_Env.uvar_subtyping);
                               FStarC_TypeChecker_Env.intactics =
                                 (env.FStarC_TypeChecker_Env.intactics);
                               FStarC_TypeChecker_Env.nocoerce =
                                 (env.FStarC_TypeChecker_Env.nocoerce);
                               FStarC_TypeChecker_Env.tc_term =
                                 (env.FStarC_TypeChecker_Env.tc_term);
                               FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                 =
                                 (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                               FStarC_TypeChecker_Env.universe_of =
                                 (env.FStarC_TypeChecker_Env.universe_of);
                               FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                 =
                                 (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                               FStarC_TypeChecker_Env.teq_nosmt_force =
                                 (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                               FStarC_TypeChecker_Env.subtype_nosmt_force =
                                 (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                               FStarC_TypeChecker_Env.qtbl_name_and_index =
                                 (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                               FStarC_TypeChecker_Env.normalized_eff_names =
                                 (env.FStarC_TypeChecker_Env.normalized_eff_names);
                               FStarC_TypeChecker_Env.fv_delta_depths =
                                 (env.FStarC_TypeChecker_Env.fv_delta_depths);
                               FStarC_TypeChecker_Env.proof_ns =
                                 (env.FStarC_TypeChecker_Env.proof_ns);
                               FStarC_TypeChecker_Env.synth_hook =
                                 (env.FStarC_TypeChecker_Env.synth_hook);
                               FStarC_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                               FStarC_TypeChecker_Env.splice =
                                 (env.FStarC_TypeChecker_Env.splice);
                               FStarC_TypeChecker_Env.mpreprocess =
                                 (env.FStarC_TypeChecker_Env.mpreprocess);
                               FStarC_TypeChecker_Env.postprocess =
                                 (env.FStarC_TypeChecker_Env.postprocess);
                               FStarC_TypeChecker_Env.identifier_info =
                                 (env.FStarC_TypeChecker_Env.identifier_info);
                               FStarC_TypeChecker_Env.tc_hooks =
                                 (env.FStarC_TypeChecker_Env.tc_hooks);
                               FStarC_TypeChecker_Env.dsenv =
                                 (env.FStarC_TypeChecker_Env.dsenv);
                               FStarC_TypeChecker_Env.nbe =
                                 (env.FStarC_TypeChecker_Env.nbe);
                               FStarC_TypeChecker_Env.strict_args_tab =
                                 (env.FStarC_TypeChecker_Env.strict_args_tab);
                               FStarC_TypeChecker_Env.erasable_types_tab =
                                 (env.FStarC_TypeChecker_Env.erasable_types_tab);
                               FStarC_TypeChecker_Env.enable_defer_to_tac =
                                 (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                               FStarC_TypeChecker_Env.unif_allow_ref_guards =
                                 (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                               FStarC_TypeChecker_Env.erase_erasable_args =
                                 (env.FStarC_TypeChecker_Env.erase_erasable_args);
                               FStarC_TypeChecker_Env.core_check =
                                 (env.FStarC_TypeChecker_Env.core_check);
                               FStarC_TypeChecker_Env.missing_decl =
                                 (env.FStarC_TypeChecker_Env.missing_decl)
                             } in
                           let lift1 =
                             match lift with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some (uvs, lift2) ->
                                 let uu___7 =
                                   let uu___8 =
                                     FStarC_Syntax_Subst.univ_var_opening uvs in
                                   match uu___8 with
                                   | (usubst, uvs1) ->
                                       let uu___9 =
                                         FStarC_TypeChecker_Env.push_univ_vars
                                           env1 uvs1 in
                                       let uu___10 =
                                         FStarC_Syntax_Subst.subst usubst
                                           lift2 in
                                       (uu___9, uu___10) in
                                 (match uu___7 with
                                  | (env2, lift3) ->
                                      let uu___8 =
                                        let uu___9 =
                                          FStarC_TypeChecker_Env.lookup_effect_lid
                                            env2
                                            sub.FStarC_Syntax_Syntax.source in
                                        monad_signature env2
                                          sub.FStarC_Syntax_Syntax.source
                                          uu___9 in
                                      (match uu___8 with
                                       | (a1, wp_a_src1) ->
                                           let wp_a =
                                             FStarC_Syntax_Syntax.new_bv
                                               FStar_Pervasives_Native.None
                                               wp_a_src1 in
                                           let a_typ =
                                             FStarC_Syntax_Syntax.bv_to_name
                                               a1 in
                                           let wp_a_typ =
                                             FStarC_Syntax_Syntax.bv_to_name
                                               wp_a in
                                           let repr_f =
                                             repr_type
                                               sub.FStarC_Syntax_Syntax.source
                                               a_typ wp_a_typ in
                                           let repr_result =
                                             let lift_wp1 =
                                               FStarC_TypeChecker_Normalize.normalize
                                                 [FStarC_TypeChecker_Env.EraseUniverses;
                                                 FStarC_TypeChecker_Env.AllowUnboundUniverses]
                                                 env2
                                                 (FStar_Pervasives_Native.snd
                                                    lift_wp) in
                                             let lift_wp_a =
                                               let uu___9 =
                                                 let uu___10 =
                                                   let uu___11 =
                                                     let uu___12 =
                                                       FStarC_Syntax_Syntax.as_arg
                                                         a_typ in
                                                     let uu___13 =
                                                       let uu___14 =
                                                         FStarC_Syntax_Syntax.as_arg
                                                           wp_a_typ in
                                                       [uu___14] in
                                                     uu___12 :: uu___13 in
                                                   {
                                                     FStarC_Syntax_Syntax.hd
                                                       = lift_wp1;
                                                     FStarC_Syntax_Syntax.args
                                                       = uu___11
                                                   } in
                                                 FStarC_Syntax_Syntax.Tm_app
                                                   uu___10 in
                                               let uu___10 =
                                                 FStarC_TypeChecker_Env.get_range
                                                   env2 in
                                               FStarC_Syntax_Syntax.mk uu___9
                                                 uu___10 in
                                             repr_type
                                               sub.FStarC_Syntax_Syntax.target
                                               a_typ lift_wp_a in
                                           let expected_k1 =
                                             let uu___9 =
                                               let uu___10 =
                                                 FStarC_Syntax_Syntax.mk_binder
                                                   a1 in
                                               let uu___11 =
                                                 let uu___12 =
                                                   FStarC_Syntax_Syntax.mk_binder
                                                     wp_a in
                                                 let uu___13 =
                                                   let uu___14 =
                                                     FStarC_Syntax_Syntax.null_binder
                                                       repr_f in
                                                   [uu___14] in
                                                 uu___12 :: uu___13 in
                                               uu___10 :: uu___11 in
                                             let uu___10 =
                                               FStarC_Syntax_Syntax.mk_Total
                                                 repr_result in
                                             FStarC_Syntax_Util.arrow uu___9
                                               uu___10 in
                                           let uu___9 =
                                             FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env2 expected_k1 in
                                           (match uu___9 with
                                            | (expected_k2, uu___10, uu___11)
                                                ->
                                                let lift4 =
                                                  if
                                                    (FStarC_Compiler_List.length
                                                       uvs)
                                                      = Prims.int_zero
                                                  then
                                                    check_and_gen1 env2 lift3
                                                      expected_k2
                                                  else
                                                    (let lift5 =
                                                       FStarC_TypeChecker_TcTerm.tc_check_trivial_guard
                                                         env2 lift3
                                                         expected_k2 in
                                                     let uu___13 =
                                                       FStarC_Syntax_Subst.close_univ_vars
                                                         uvs lift5 in
                                                     (uvs, uu___13)) in
                                                FStar_Pervasives_Native.Some
                                                  lift4))) in
                           (if
                              (FStarC_Compiler_List.length
                                 (FStar_Pervasives_Native.fst lift_wp))
                                <> Prims.int_one
                            then
                              (let uu___8 =
                                 let uu___9 =
                                   FStarC_Class_Show.show
                                     FStarC_Ident.showable_lident
                                     sub.FStarC_Syntax_Syntax.source in
                                 let uu___10 =
                                   FStarC_Class_Show.show
                                     FStarC_Ident.showable_lident
                                     sub.FStarC_Syntax_Syntax.target in
                                 let uu___11 =
                                   FStarC_Compiler_Util.string_of_int
                                     (FStarC_Compiler_List.length
                                        (FStar_Pervasives_Native.fst lift_wp)) in
                                 FStarC_Compiler_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu___9 uu___10 uu___11 in
                               FStarC_Errors.raise_error
                                 FStarC_Class_HasRange.hasRange_range r
                                 FStarC_Errors_Codes.Fatal_TooManyUniverse ()
                                 (Obj.magic
                                    FStarC_Errors_Msg.is_error_message_string)
                                 (Obj.magic uu___8))
                            else ();
                            (let uu___9 =
                               (FStarC_Compiler_Util.is_some lift1) &&
                                 (let uu___10 =
                                    let uu___11 =
                                      let uu___12 =
                                        FStarC_Compiler_Util.must lift1 in
                                      FStar_Pervasives_Native.fst uu___12 in
                                    FStarC_Compiler_List.length uu___11 in
                                  uu___10 <> Prims.int_one) in
                             if uu___9
                             then
                               let uu___10 =
                                 let uu___11 =
                                   FStarC_Class_Show.show
                                     FStarC_Ident.showable_lident
                                     sub.FStarC_Syntax_Syntax.source in
                                 let uu___12 =
                                   FStarC_Class_Show.show
                                     FStarC_Ident.showable_lident
                                     sub.FStarC_Syntax_Syntax.target in
                                 let uu___13 =
                                   let uu___14 =
                                     let uu___15 =
                                       let uu___16 =
                                         FStarC_Compiler_Util.must lift1 in
                                       FStar_Pervasives_Native.fst uu___16 in
                                     FStarC_Compiler_List.length uu___15 in
                                   FStarC_Compiler_Util.string_of_int uu___14 in
                                 FStarC_Compiler_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu___11 uu___12 uu___13 in
                               FStarC_Errors.raise_error
                                 FStarC_Class_HasRange.hasRange_range r
                                 FStarC_Errors_Codes.Fatal_TooManyUniverse ()
                                 (Obj.magic
                                    FStarC_Errors_Msg.is_error_message_string)
                                 (Obj.magic uu___10)
                             else ());
                            {
                              FStarC_Syntax_Syntax.source =
                                (sub.FStarC_Syntax_Syntax.source);
                              FStarC_Syntax_Syntax.target =
                                (sub.FStarC_Syntax_Syntax.target);
                              FStarC_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStarC_Syntax_Syntax.lift = lift1;
                              FStarC_Syntax_Syntax.kind =
                                (sub.FStarC_Syntax_Syntax.kind)
                            }))))))
let (tc_effect_abbrev :
  FStarC_TypeChecker_Env.env ->
    (FStarC_Ident.lident * FStarC_Syntax_Syntax.univ_names *
      FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.comp) ->
      FStarC_Compiler_Range_Type.range ->
        (FStarC_Ident.lident * FStarC_Syntax_Syntax.univ_names *
          FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.comp))
  =
  fun env ->
    fun uu___ ->
      fun r ->
        match uu___ with
        | (lid, uvs, tps, c) ->
            let env0 = env in
            let uu___1 =
              if (FStarC_Compiler_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu___3 = FStarC_Syntax_Subst.univ_var_opening uvs in
                 match uu___3 with
                 | (usubst, uvs1) ->
                     let tps1 = FStarC_Syntax_Subst.subst_binders usubst tps in
                     let c1 =
                       let uu___4 =
                         FStarC_Syntax_Subst.shift_subst
                           (FStarC_Compiler_List.length tps1) usubst in
                       FStarC_Syntax_Subst.subst_comp uu___4 c in
                     let uu___4 =
                       FStarC_TypeChecker_Env.push_univ_vars env uvs1 in
                     (uu___4, uvs1, tps1, c1)) in
            (match uu___1 with
             | (env1, uvs1, tps1, c1) ->
                 let env2 = FStarC_TypeChecker_Env.set_range env1 r in
                 let uu___2 = FStarC_Syntax_Subst.open_comp tps1 c1 in
                 (match uu___2 with
                  | (tps2, c2) ->
                      let uu___3 =
                        FStarC_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                      (match uu___3 with
                       | (tps3, env3, us) ->
                           let uu___4 =
                             FStarC_TypeChecker_TcTerm.tc_comp env3 c2 in
                           (match uu___4 with
                            | (c3, u, g) ->
                                let is_default_effect =
                                  let uu___5 =
                                    FStarC_TypeChecker_Env.get_default_effect
                                      env3
                                      (FStarC_Syntax_Util.comp_effect_name c3) in
                                  match uu___5 with
                                  | FStar_Pervasives_Native.None -> false
                                  | FStar_Pervasives_Native.Some l ->
                                      FStarC_Ident.lid_equals l lid in
                                (FStarC_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | { FStarC_Syntax_Syntax.binder_bv = x;
                                        FStarC_Syntax_Syntax.binder_qual =
                                          uu___7;
                                        FStarC_Syntax_Syntax.binder_positivity
                                          = uu___8;
                                        FStarC_Syntax_Syntax.binder_attrs =
                                          uu___9;_}::tl
                                        ->
                                        (if
                                           is_default_effect &&
                                             (Prims.op_Negation (tl = []))
                                         then
                                           (let uu___11 =
                                              let uu___12 =
                                                FStarC_Ident.string_of_lid
                                                  lid in
                                              let uu___13 =
                                                FStarC_Ident.string_of_lid
                                                  (FStarC_Syntax_Util.comp_effect_name
                                                     c3) in
                                              FStarC_Compiler_Util.format2
                                                "Effect %s is marked as a default effect for %s, but it has more than one arguments"
                                                uu___12 uu___13 in
                                            FStarC_Errors.raise_error
                                              FStarC_Class_HasRange.hasRange_range
                                              r
                                              FStarC_Errors_Codes.Fatal_UnexpectedEffect
                                              ()
                                              (Obj.magic
                                                 FStarC_Errors_Msg.is_error_message_string)
                                              (Obj.magic uu___11))
                                         else ();
                                         FStarC_Syntax_Syntax.bv_to_name x)
                                    | uu___7 ->
                                        FStarC_Errors.raise_error
                                          FStarC_Class_HasRange.hasRange_range
                                          r
                                          FStarC_Errors_Codes.Fatal_NotEnoughArgumentsForEffect
                                          ()
                                          (Obj.magic
                                             FStarC_Errors_Msg.is_error_message_string)
                                          (Obj.magic
                                             "Effect abbreviations must bind at least the result type") in
                                  let def_result_typ =
                                    FStarC_Syntax_Util.comp_result c3 in
                                  let uu___7 =
                                    let uu___8 =
                                      FStarC_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ in
                                    Prims.op_Negation uu___8 in
                                  if uu___7
                                  then
                                    let uu___8 =
                                      let uu___9 =
                                        FStarC_Class_Show.show
                                          FStarC_Syntax_Print.showable_term
                                          expected_result_typ in
                                      let uu___10 =
                                        FStarC_Class_Show.show
                                          FStarC_Syntax_Print.showable_term
                                          def_result_typ in
                                      FStarC_Compiler_Util.format2
                                        "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                        uu___9 uu___10 in
                                    FStarC_Errors.raise_error
                                      FStarC_Class_HasRange.hasRange_range r
                                      FStarC_Errors_Codes.Fatal_EffectAbbreviationResultTypeMismatch
                                      ()
                                      (Obj.magic
                                         FStarC_Errors_Msg.is_error_message_string)
                                      (Obj.magic uu___8)
                                  else ());
                                 (let tps4 =
                                    FStarC_Syntax_Subst.close_binders tps3 in
                                  let c4 =
                                    FStarC_Syntax_Subst.close_comp tps4 c3 in
                                  let uu___7 =
                                    let uu___8 =
                                      FStarC_Syntax_Syntax.mk
                                        (FStarC_Syntax_Syntax.Tm_arrow
                                           {
                                             FStarC_Syntax_Syntax.bs1 = tps4;
                                             FStarC_Syntax_Syntax.comp = c4
                                           }) r in
                                    FStarC_TypeChecker_Generalize.generalize_universes
                                      env0 uu___8 in
                                  match uu___7 with
                                  | (uvs2, t) ->
                                      let uu___8 =
                                        let uu___9 =
                                          let uu___10 =
                                            let uu___11 =
                                              FStarC_Syntax_Subst.compress t in
                                            uu___11.FStarC_Syntax_Syntax.n in
                                          (tps4, uu___10) in
                                        match uu___9 with
                                        | ([], FStarC_Syntax_Syntax.Tm_arrow
                                           {
                                             FStarC_Syntax_Syntax.bs1 =
                                               uu___10;
                                             FStarC_Syntax_Syntax.comp = c5;_})
                                            -> ([], c5)
                                        | (uu___10,
                                           FStarC_Syntax_Syntax.Tm_arrow
                                           { FStarC_Syntax_Syntax.bs1 = tps5;
                                             FStarC_Syntax_Syntax.comp = c5;_})
                                            -> (tps5, c5)
                                        | uu___10 ->
                                            failwith
                                              "Impossible (t is an arrow)" in
                                      (match uu___8 with
                                       | (tps5, c5) ->
                                           (if
                                              (FStarC_Compiler_List.length
                                                 uvs2)
                                                <> Prims.int_one
                                            then
                                              (let uu___10 =
                                                 FStarC_Syntax_Subst.open_univ_vars
                                                   uvs2 t in
                                               match uu___10 with
                                               | (uu___11, t1) ->
                                                   let uu___12 =
                                                     let uu___13 =
                                                       FStarC_Class_Show.show
                                                         FStarC_Ident.showable_lident
                                                         lid in
                                                     let uu___14 =
                                                       FStarC_Class_Show.show
                                                         FStarC_Class_Show.showable_nat
                                                         (FStarC_Compiler_List.length
                                                            uvs2) in
                                                     let uu___15 =
                                                       FStarC_Class_Show.show
                                                         FStarC_Syntax_Print.showable_term
                                                         t1 in
                                                     FStarC_Compiler_Util.format3
                                                       "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                       uu___13 uu___14
                                                       uu___15 in
                                                   FStarC_Errors.raise_error
                                                     FStarC_Class_HasRange.hasRange_range
                                                     r
                                                     FStarC_Errors_Codes.Fatal_TooManyUniverse
                                                     ()
                                                     (Obj.magic
                                                        FStarC_Errors_Msg.is_error_message_string)
                                                     (Obj.magic uu___12))
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
let (check_polymonadic_bind_for_erasable_effects :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Ident.lident ->
        FStarC_Ident.lident -> FStarC_Compiler_Range_Type.range -> unit)
  =
  fun env ->
    fun m ->
      fun n ->
        fun p ->
          fun r ->
            let err reason =
              let uu___ =
                let uu___1 =
                  FStarC_Class_Show.show FStarC_Ident.showable_lident m in
                let uu___2 =
                  FStarC_Class_Show.show FStarC_Ident.showable_lident n in
                let uu___3 =
                  FStarC_Class_Show.show FStarC_Ident.showable_lident p in
                FStarC_Compiler_Util.format4
                  "Error definition polymonadic bind (%s, %s) |> %s: %s"
                  uu___1 uu___2 uu___3 reason in
              FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
                r FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                (Obj.magic uu___) in
            let m1 = FStarC_TypeChecker_Env.norm_eff_name env m in
            let n1 = FStarC_TypeChecker_Env.norm_eff_name env n in
            let uu___ =
              (FStarC_Ident.lid_equals m1
                 FStarC_Parser_Const.effect_GHOST_lid)
                ||
                (FStarC_Ident.lid_equals n1
                   FStarC_Parser_Const.effect_GHOST_lid) in
            if uu___
            then
              err
                "GHOST computations are not allowed to be composed using user-defined polymonadic binds"
            else
              (let m_erasable =
                 FStarC_TypeChecker_Env.is_erasable_effect env m1 in
               let n_erasable =
                 FStarC_TypeChecker_Env.is_erasable_effect env n1 in
               let p_erasable =
                 FStarC_TypeChecker_Env.is_erasable_effect env p in
               if p_erasable
               then
                 let uu___2 =
                   (Prims.op_Negation m_erasable) &&
                     (let uu___3 =
                        FStarC_Ident.lid_equals m1
                          FStarC_Parser_Const.effect_PURE_lid in
                      Prims.op_Negation uu___3) in
                 (if uu___2
                  then
                    let uu___3 =
                      let uu___4 = FStarC_Ident.string_of_lid m1 in
                      FStarC_Compiler_Util.format1
                        "target effect is erasable but %s is neither erasable nor PURE"
                        uu___4 in
                    err uu___3
                  else
                    (let uu___4 =
                       (Prims.op_Negation n_erasable) &&
                         (let uu___5 =
                            FStarC_Ident.lid_equals n1
                              FStarC_Parser_Const.effect_PURE_lid in
                          Prims.op_Negation uu___5) in
                     if uu___4
                     then
                       let uu___5 =
                         let uu___6 = FStarC_Ident.string_of_lid n1 in
                         FStarC_Compiler_Util.format1
                           "target effect is erasable but %s is neither erasable nor PURE"
                           uu___6 in
                       err uu___5
                     else ()))
               else ())
let (tc_polymonadic_bind :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Ident.lident ->
        FStarC_Ident.lident ->
          FStarC_Syntax_Syntax.tscheme ->
            (FStarC_Syntax_Syntax.tscheme * FStarC_Syntax_Syntax.tscheme *
              FStarC_Syntax_Syntax.indexed_effect_combinator_kind))
  =
  fun env ->
    fun m ->
      fun n ->
        fun p ->
          fun ts ->
            let eff_name =
              let uu___ =
                let uu___1 = FStarC_Ident.ident_of_lid m in
                FStarC_Ident.string_of_id uu___1 in
              let uu___1 =
                let uu___2 = FStarC_Ident.ident_of_lid n in
                FStarC_Ident.string_of_id uu___2 in
              let uu___2 =
                let uu___3 = FStarC_Ident.ident_of_lid p in
                FStarC_Ident.string_of_id uu___3 in
              FStarC_Compiler_Util.format3 "(%s, %s) |> %s)" uu___ uu___1
                uu___2 in
            let r = (FStar_Pervasives_Native.snd ts).FStarC_Syntax_Syntax.pos in
            check_polymonadic_bind_for_erasable_effects env m n p r;
            (let uu___1 =
               check_and_gen env eff_name "polymonadic_bind"
                 (Prims.of_int (2)) ts in
             match uu___1 with
             | (us, t, ty) ->
                 let uu___2 = FStarC_Syntax_Subst.open_univ_vars us ty in
                 (match uu___2 with
                  | (us1, ty1) ->
                      let env1 =
                        FStarC_TypeChecker_Env.push_univ_vars env us1 in
                      let uu___3 =
                        let uu___4 =
                          FStarC_TypeChecker_Env.get_effect_decl env1 m in
                        let uu___5 =
                          FStarC_TypeChecker_Env.get_effect_decl env1 n in
                        let uu___6 =
                          FStarC_TypeChecker_Env.get_effect_decl env1 p in
                        (uu___4, uu___5, uu___6) in
                      (match uu___3 with
                       | (m_ed, n_ed, p_ed) ->
                           let uu___4 =
                             let uu___5 =
                               FStarC_Syntax_Util.effect_sig_ts
                                 m_ed.FStarC_Syntax_Syntax.signature in
                             let uu___6 =
                               FStarC_Syntax_Util.effect_sig_ts
                                 n_ed.FStarC_Syntax_Syntax.signature in
                             let uu___7 =
                               FStarC_Syntax_Util.effect_sig_ts
                                 p_ed.FStarC_Syntax_Syntax.signature in
                             let uu___8 =
                               FStarC_Syntax_Util.get_eff_repr m_ed in
                             let uu___9 =
                               FStarC_Syntax_Util.get_eff_repr n_ed in
                             let uu___10 =
                               FStarC_Syntax_Util.get_eff_repr p_ed in
                             let uu___11 =
                               FStarC_TypeChecker_Env.get_range env1 in
                             validate_indexed_effect_bind_shape env1 m n p
                               uu___5 uu___6 uu___7 uu___8 uu___9 uu___10 us1
                               ty1 uu___11 Prims.int_zero false in
                           (match uu___4 with
                            | (k, kind) ->
                                ((let uu___6 =
                                    FStarC_Compiler_Debug.extreme () in
                                  if uu___6
                                  then
                                    let uu___7 =
                                      FStarC_Syntax_Print.tscheme_to_string
                                        (us1, t) in
                                    let uu___8 =
                                      FStarC_Syntax_Print.tscheme_to_string
                                        (us1, k) in
                                    FStarC_Compiler_Util.print3
                                      "Polymonadic bind %s after typechecking (%s::%s)\n"
                                      eff_name uu___7 uu___8
                                  else ());
                                 (let uu___7 =
                                    let uu___8 =
                                      let uu___9 =
                                        FStarC_Compiler_Util.format1
                                          "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                          eff_name in
                                      FStarC_Errors_Msg.text uu___9 in
                                    [uu___8] in
                                  FStarC_Errors.log_issue
                                    FStarC_Class_HasRange.hasRange_range r
                                    FStarC_Errors_Codes.Warning_BleedingEdge_Feature
                                    ()
                                    (Obj.magic
                                       FStarC_Errors_Msg.is_error_message_list_doc)
                                    (Obj.magic uu___7));
                                 (let uu___7 =
                                    let uu___8 =
                                      FStarC_Syntax_Subst.close_univ_vars us1
                                        k in
                                    (us1, uu___8) in
                                  ((us1, t), uu___7, kind)))))))
let (tc_polymonadic_subcomp :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      FStarC_Ident.lident ->
        FStarC_Syntax_Syntax.tscheme ->
          (FStarC_Syntax_Syntax.tscheme * FStarC_Syntax_Syntax.tscheme *
            FStarC_Syntax_Syntax.indexed_effect_combinator_kind))
  =
  fun env0 ->
    fun m ->
      fun n ->
        fun ts ->
          let r = (FStar_Pervasives_Native.snd ts).FStarC_Syntax_Syntax.pos in
          check_lift_for_erasable_effects env0 m n r;
          (let combinator_name =
             let uu___1 =
               let uu___2 = FStarC_Ident.ident_of_lid m in
               FStarC_Ident.string_of_id uu___2 in
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStarC_Ident.ident_of_lid n in
                 FStarC_Ident.string_of_id uu___4 in
               Prims.strcat " <: " uu___3 in
             Prims.strcat uu___1 uu___2 in
           let uu___1 =
             check_and_gen env0 combinator_name "polymonadic_subcomp"
               Prims.int_one ts in
           match uu___1 with
           | (us, t, ty) ->
               let uu___2 = FStarC_Syntax_Subst.open_univ_vars us ty in
               (match uu___2 with
                | (us1, ty1) ->
                    let env = FStarC_TypeChecker_Env.push_univ_vars env0 us1 in
                    let uu___3 =
                      let uu___4 =
                        FStarC_TypeChecker_Env.get_effect_decl env m in
                      let uu___5 =
                        FStarC_TypeChecker_Env.get_effect_decl env n in
                      (uu___4, uu___5) in
                    (match uu___3 with
                     | (m_ed, n_ed) ->
                         let uu___4 =
                           let uu___5 =
                             FStarC_Syntax_Util.effect_sig_ts
                               m_ed.FStarC_Syntax_Syntax.signature in
                           let uu___6 =
                             FStarC_Syntax_Util.effect_sig_ts
                               n_ed.FStarC_Syntax_Syntax.signature in
                           let uu___7 = FStarC_Syntax_Util.get_eff_repr m_ed in
                           let uu___8 = FStarC_Syntax_Util.get_eff_repr n_ed in
                           let uu___9 = FStarC_Compiler_List.hd us1 in
                           let uu___10 = FStarC_TypeChecker_Env.get_range env in
                           validate_indexed_effect_subcomp_shape env m n
                             uu___5 uu___6 uu___7 uu___8 uu___9 ty1
                             Prims.int_zero uu___10 in
                         (match uu___4 with
                          | (k, kind) ->
                              ((let uu___6 = FStarC_Compiler_Debug.extreme () in
                                if uu___6
                                then
                                  let uu___7 =
                                    FStarC_Syntax_Print.tscheme_to_string
                                      (us1, t) in
                                  let uu___8 =
                                    FStarC_Syntax_Print.tscheme_to_string
                                      (us1, k) in
                                  FStarC_Compiler_Util.print3
                                    "Polymonadic subcomp %s after typechecking (%s::%s)\n"
                                    combinator_name uu___7 uu___8
                                else ());
                               (let uu___7 =
                                  let uu___8 =
                                    let uu___9 =
                                      FStarC_Compiler_Util.format1
                                        "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                        combinator_name in
                                    FStarC_Errors_Msg.text uu___9 in
                                  [uu___8] in
                                FStarC_Errors.log_issue
                                  FStarC_Class_HasRange.hasRange_range r
                                  FStarC_Errors_Codes.Warning_BleedingEdge_Feature
                                  ()
                                  (Obj.magic
                                     FStarC_Errors_Msg.is_error_message_list_doc)
                                  (Obj.magic uu___7));
                               (let uu___7 =
                                  let uu___8 =
                                    FStarC_Syntax_Subst.close_univ_vars us1 k in
                                  (us1, uu___8) in
                                ((us1, t), uu___7, kind)))))))