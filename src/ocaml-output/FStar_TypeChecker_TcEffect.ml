open Prims
let (dmff_cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  = fun env -> fun ed -> FStar_TypeChecker_DMFF.cps_and_elaborate env ed
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.string ->
        Prims.int ->
          (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) ->
            (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term *
              FStar_Syntax_Syntax.typ))
  =
  fun env ->
    fun eff_name ->
      fun comb ->
        fun n ->
          fun uu___ ->
            match uu___ with
            | (us, t) ->
                let uu___1 = FStar_Syntax_Subst.open_univ_vars us t in
                (match uu___1 with
                 | (us1, t1) ->
                     let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           FStar_TypeChecker_Env.push_univ_vars env us1 in
                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term uu___4
                           t1 in
                       match uu___3 with
                       | (t2, lc, g) ->
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (t2, (lc.FStar_TypeChecker_Common.res_typ))) in
                     (match uu___2 with
                      | (t2, ty) ->
                          let uu___3 =
                            FStar_TypeChecker_Generalize.generalize_universes
                              env t2 in
                          (match uu___3 with
                           | (g_us, t3) ->
                               let ty1 =
                                 FStar_Syntax_Subst.close_univ_vars g_us ty in
                               (if (FStar_Compiler_List.length g_us) <> n
                                then
                                  (let error =
                                     let uu___4 =
                                       FStar_Compiler_Util.string_of_int n in
                                     let uu___5 =
                                       let uu___6 =
                                         FStar_Compiler_Effect.op_Bar_Greater
                                           g_us FStar_Compiler_List.length in
                                       FStar_Compiler_Effect.op_Bar_Greater
                                         uu___6
                                         FStar_Compiler_Util.string_of_int in
                                     let uu___6 =
                                       FStar_Syntax_Print.tscheme_to_string
                                         (g_us, t3) in
                                     FStar_Compiler_Util.format5
                                       "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
                                       eff_name comb uu___4 uu___5 uu___6 in
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                       error) t3.FStar_Syntax_Syntax.pos;
                                   (match us1 with
                                    | [] -> ()
                                    | uu___5 ->
                                        let uu___6 =
                                          ((FStar_Compiler_List.length us1) =
                                             (FStar_Compiler_List.length g_us))
                                            &&
                                            (FStar_Compiler_List.forall2
                                               (fun u1 ->
                                                  fun u2 ->
                                                    let uu___7 =
                                                      FStar_Syntax_Syntax.order_univ_name
                                                        u1 u2 in
                                                    uu___7 = Prims.int_zero)
                                               us1 g_us) in
                                        if uu___6
                                        then ()
                                        else
                                          (let uu___8 =
                                             let uu___9 =
                                               let uu___10 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   us1 in
                                               let uu___11 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   g_us in
                                               FStar_Compiler_Util.format4
                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                 eff_name comb uu___10
                                                 uu___11 in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu___9) in
                                           FStar_Errors.raise_error uu___8
                                             t3.FStar_Syntax_Syntax.pos)))
                                else ();
                                (g_us, t3, ty1)))))
let (pure_wp_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      Prims.string ->
        FStar_Compiler_Range.range ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun t ->
      fun reason ->
        fun r ->
          let pure_wp_t =
            let pure_wp_ts =
              let uu___ =
                FStar_TypeChecker_Env.lookup_definition
                  [FStar_TypeChecker_Env.NoDelta] env
                  FStar_Parser_Const.pure_wp_lid in
              FStar_Compiler_Effect.op_Bar_Greater uu___
                FStar_Compiler_Util.must in
            let uu___ = FStar_TypeChecker_Env.inst_tscheme pure_wp_ts in
            match uu___ with
            | (uu___1, pure_wp_t1) ->
                let uu___2 =
                  let uu___3 =
                    FStar_Compiler_Effect.op_Bar_Greater t
                      FStar_Syntax_Syntax.as_arg in
                  [uu___3] in
                FStar_Syntax_Syntax.mk_Tm_app pure_wp_t1 uu___2 r in
          let uu___ =
            FStar_TypeChecker_Env.new_implicit_var reason r env pure_wp_t
              (FStar_Syntax_Syntax.Allow_untyped "wp")
              FStar_Pervasives_Native.None in
          match uu___ with
          | (pure_wp_uvar1, uu___1, guard_wp) -> (pure_wp_uvar1, guard_wp)

let (validate_layered_effect_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      Prims.bool -> FStar_Compiler_Range.range -> unit)
  =
  fun env ->
    fun bs ->
      fun check_non_informatve_binders ->
        fun r ->
          if check_non_informatve_binders
          then
            let uu___ =
              FStar_Compiler_List.fold_left
                (fun uu___1 ->
                   fun b ->
                     match uu___1 with
                     | (env1, bs1) ->
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b] in
                         let uu___2 =
                           FStar_TypeChecker_Normalize.non_info_norm env2
                             (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                         if uu___2 then (env2, bs1) else (env2, (b :: bs1)))
                (env, []) bs in
            match uu___ with
            | (uu___1, informative_binders) ->
                (if
                   (FStar_Compiler_List.length informative_binders) <>
                     Prims.int_zero
                 then
                   let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         FStar_Syntax_Print.binders_to_string "; "
                           informative_binders in
                       FStar_Compiler_Util.format1
                         "Binders %s are informative while the effect is reifiable"
                         uu___4 in
                     (FStar_Errors.Fatal_UnexpectedEffect, uu___3) in
                   FStar_Errors.raise_error uu___2 r
                 else ())
          else ()
let (print_binder_kinds :
  FStar_Syntax_Syntax.indexed_effect_binder_kind Prims.list -> Prims.string)
  =
  fun l ->
    FStar_Compiler_List.fold_left
      (fun s ->
         fun k ->
           Prims.op_Hat s
             (Prims.op_Hat "; "
                (match k with
                 | FStar_Syntax_Syntax.Type_binder -> "type"
                 | FStar_Syntax_Syntax.Substitution_binder -> "sub"
                 | FStar_Syntax_Syntax.BindCont_no_abstraction_binder ->
                     "g_no_abs"
                 | FStar_Syntax_Syntax.Ad_hoc_binder -> "ad_hoc"
                 | FStar_Syntax_Syntax.Repr_binder -> "repr"))) "" l
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
let (bind_combinator_kind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme ->
            FStar_Syntax_Syntax.tscheme ->
              FStar_Syntax_Syntax.tscheme ->
                FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ->
                  FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option
                    ->
                    FStar_Syntax_Syntax.tscheme
                      FStar_Pervasives_Native.option ->
                      FStar_Syntax_Syntax.univ_names ->
                        FStar_Syntax_Syntax.typ ->
                          Prims.bool ->
                            FStar_Syntax_Syntax.indexed_effect_binder_kind
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
                          fun has_range_binders ->
                            let uu___ = bind_us in
                            match uu___ with
                            | u_a::u_b::[] ->
                                let uu___1 =
                                  let uu___2 =
                                    FStar_Compiler_Effect.op_Bar_Greater k
                                      FStar_Syntax_Util.arrow_formals in
                                  FStar_Compiler_Effect.op_Bar_Greater uu___2
                                    FStar_Pervasives_Native.fst in
                                (match uu___1 with
                                 | a_b::b_b::rest_bs ->
                                     let f_sig_bs =
                                       let uu___2 =
                                         FStar_TypeChecker_Env.inst_tscheme_with
                                           m_sig_ts
                                           [FStar_Syntax_Syntax.U_name u_a] in
                                       match uu___2 with
                                       | (uu___3, sig1) ->
                                           let uu___4 =
                                             let uu___5 =
                                               FStar_Compiler_Effect.op_Bar_Greater
                                                 sig1
                                                 FStar_Syntax_Util.arrow_formals in
                                             FStar_Compiler_Effect.op_Bar_Greater
                                               uu___5
                                               FStar_Pervasives_Native.fst in
                                           FStar_Compiler_Effect.op_Bar_Greater
                                             uu___4
                                             (fun uu___5 ->
                                                match uu___5 with
                                                | a::bs ->
                                                    let uu___6 =
                                                      let uu___7 =
                                                        let uu___8 =
                                                          let uu___9 =
                                                            FStar_Compiler_Effect.op_Bar_Greater
                                                              a_b.FStar_Syntax_Syntax.binder_bv
                                                              FStar_Syntax_Syntax.bv_to_name in
                                                          ((a.FStar_Syntax_Syntax.binder_bv),
                                                            uu___9) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu___8 in
                                                      [uu___7] in
                                                    FStar_Syntax_Subst.subst_binders
                                                      uu___6 bs) in
                                     let uu___2 =
                                       if
                                         (FStar_Compiler_List.length rest_bs)
                                           <
                                           (FStar_Compiler_List.length
                                              f_sig_bs)
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu___4 =
                                            FStar_Compiler_List.splitAt
                                              (FStar_Compiler_List.length
                                                 f_sig_bs) rest_bs in
                                          FStar_Compiler_Effect.op_Bar_Greater
                                            uu___4
                                            (fun uu___5 ->
                                               FStar_Pervasives_Native.Some
                                                 uu___5)) in
                                     op_let_Question uu___2
                                       (fun uu___3 ->
                                          match uu___3 with
                                          | (f_bs, rest_bs1) ->
                                              let uu___4 =
                                                let f_bs_kinds =
                                                  FStar_Compiler_List.map2
                                                    (fun f_sig_b ->
                                                       fun f_b ->
                                                         let uu___5 =
                                                           let uu___6 =
                                                             FStar_Syntax_Util.eq_tm
                                                               (f_sig_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                                               (f_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                                           uu___6 =
                                                             FStar_Syntax_Util.Equal in
                                                         if uu___5
                                                         then
                                                           FStar_Syntax_Syntax.Substitution_binder
                                                         else
                                                           FStar_Syntax_Syntax.Ad_hoc_binder)
                                                    f_sig_bs f_bs in
                                                if
                                                  FStar_Compiler_List.contains
                                                    FStar_Syntax_Syntax.Ad_hoc_binder
                                                    f_bs_kinds
                                                then
                                                  FStar_Pervasives_Native.None
                                                else
                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                    f_bs_kinds
                                                    (fun uu___6 ->
                                                       FStar_Pervasives_Native.Some
                                                         uu___6) in
                                              op_let_Question uu___4
                                                (fun f_bs_kinds ->
                                                   let g_sig_bs =
                                                     let uu___5 =
                                                       FStar_TypeChecker_Env.inst_tscheme_with
                                                         n_sig_ts
                                                         [FStar_Syntax_Syntax.U_name
                                                            u_b] in
                                                     match uu___5 with
                                                     | (uu___6, sig1) ->
                                                         let uu___7 =
                                                           let uu___8 =
                                                             FStar_Compiler_Effect.op_Bar_Greater
                                                               sig1
                                                               FStar_Syntax_Util.arrow_formals in
                                                           FStar_Compiler_Effect.op_Bar_Greater
                                                             uu___8
                                                             FStar_Pervasives_Native.fst in
                                                         FStar_Compiler_Effect.op_Bar_Greater
                                                           uu___7
                                                           (fun uu___8 ->
                                                              match uu___8
                                                              with
                                                              | b::bs ->
                                                                  let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    b_b.FStar_Syntax_Syntax.binder_bv
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    ((b.FStar_Syntax_Syntax.binder_bv),
                                                                    uu___12) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu___11 in
                                                                    [uu___10] in
                                                                  FStar_Syntax_Subst.subst_binders
                                                                    uu___9 bs) in
                                                   let uu___5 =
                                                     if
                                                       (FStar_Compiler_List.length
                                                          rest_bs1)
                                                         <
                                                         (FStar_Compiler_List.length
                                                            g_sig_bs)
                                                     then
                                                       FStar_Pervasives_Native.None
                                                     else
                                                       (let uu___7 =
                                                          FStar_Compiler_List.splitAt
                                                            (FStar_Compiler_List.length
                                                               g_sig_bs)
                                                            rest_bs1 in
                                                        FStar_Compiler_Effect.op_Bar_Greater
                                                          uu___7
                                                          (fun uu___8 ->
                                                             FStar_Pervasives_Native.Some
                                                               uu___8)) in
                                                   op_let_Question uu___5
                                                     (fun uu___6 ->
                                                        match uu___6 with
                                                        | (g_bs, rest_bs2) ->
                                                            let uu___7 =
                                                              let g_bs_kinds
                                                                =
                                                                FStar_Compiler_List.map2
                                                                  (fun
                                                                    g_sig_b
                                                                    ->
                                                                    fun g_b
                                                                    ->
                                                                    let g_sig_b_arrow_t
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    a_b.FStar_Syntax_Syntax.binder_bv
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "x"
                                                                    FStar_Pervasives_Native.None
                                                                    uu___11 in
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    uu___10 in
                                                                    [uu___9] in
                                                                    let uu___9
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    (g_sig_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu___8
                                                                    uu___9 in
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStar_Syntax_Util.eq_tm
                                                                    g_sig_b_arrow_t
                                                                    (g_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                                                    uu___9 =
                                                                    FStar_Syntax_Util.Equal in
                                                                    if uu___8
                                                                    then
                                                                    FStar_Syntax_Syntax.Substitution_binder
                                                                    else
                                                                    (let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStar_Syntax_Util.eq_tm
                                                                    (g_sig_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                                                    (g_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                                                    uu___11 =
                                                                    FStar_Syntax_Util.Equal in
                                                                    if
                                                                    uu___10
                                                                    then
                                                                    FStar_Syntax_Syntax.BindCont_no_abstraction_binder
                                                                    else
                                                                    FStar_Syntax_Syntax.Ad_hoc_binder))
                                                                  g_sig_bs
                                                                  g_bs in
                                                              if
                                                                FStar_Compiler_List.contains
                                                                  FStar_Syntax_Syntax.Ad_hoc_binder
                                                                  g_bs_kinds
                                                              then
                                                                FStar_Pervasives_Native.None
                                                              else
                                                                FStar_Compiler_Effect.op_Bar_Greater
                                                                  g_bs_kinds
                                                                  (fun uu___9
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___9) in
                                                            op_let_Question
                                                              uu___7
                                                              (fun g_bs_kinds
                                                                 ->
                                                                 let uu___8 =
                                                                   if
                                                                    has_range_binders
                                                                   then
                                                                    FStar_Compiler_List.splitAt
                                                                    (Prims.of_int (2))
                                                                    rest_bs2
                                                                   else
                                                                    ([],
                                                                    rest_bs2) in
                                                                 match uu___8
                                                                 with
                                                                 | (range_bs,
                                                                    rest_bs3)
                                                                    ->
                                                                    let uu___9
                                                                    = uu___8 in
                                                                    let uu___10
                                                                    =
                                                                    if
                                                                    (FStar_Compiler_List.length
                                                                    rest_bs3)
                                                                    >=
                                                                    (Prims.of_int (2))
                                                                    then
                                                                    let uu___11
                                                                    =
                                                                    FStar_Compiler_List.splitAt
                                                                    ((FStar_Compiler_List.length
                                                                    rest_bs3)
                                                                    -
                                                                    (Prims.of_int (2)))
                                                                    rest_bs3 in
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (rest_bs4,
                                                                    f_b::g_b::[])
                                                                    ->
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    (rest_bs4,
                                                                    f_b, g_b)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___12)
                                                                    else
                                                                    FStar_Pervasives_Native.None in
                                                                    op_let_Question
                                                                    uu___10
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (rest_bs4,
                                                                    f_b, g_b)
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    let expected_f_b_sort
                                                                    =
                                                                    match m_repr_ts
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    repr_ts
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme_with
                                                                    repr_ts
                                                                    [
                                                                    FStar_Syntax_Syntax.U_name
                                                                    u_a] in
                                                                    (match uu___13
                                                                    with
                                                                    | 
                                                                    (uu___14,
                                                                    t) ->
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    a_b.FStar_Syntax_Syntax.binder_bv
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___17
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                    let uu___17
                                                                    =
                                                                    FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    match uu___18
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = b;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___19;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___20;_}
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    b
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___21
                                                                    FStar_Syntax_Syntax.as_arg)
                                                                    f_bs in
                                                                    uu___16
                                                                    ::
                                                                    uu___17 in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    t uu___15
                                                                    FStar_Compiler_Range.dummyRange)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    [uu___14] in
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    a_b.FStar_Syntax_Syntax.binder_bv
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    let uu___17
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    f_bs
                                                                    (FStar_Compiler_List.map
                                                                    (fun b ->
                                                                    let uu___18
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    b.FStar_Syntax_Syntax.binder_bv
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___18
                                                                    FStar_Syntax_Syntax.as_arg)) in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    [
                                                                    FStar_Syntax_Syntax.U_name
                                                                    u_a];
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    m_eff_name;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = uu___16;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    = uu___17;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    uu___15 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu___13
                                                                    uu___14 in
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStar_Syntax_Util.eq_tm
                                                                    (f_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                                                    expected_f_b_sort in
                                                                    uu___14 =
                                                                    FStar_Syntax_Util.Equal in
                                                                    if
                                                                    uu___13
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    ()
                                                                    else
                                                                    FStar_Pervasives_Native.None in
                                                                    op_let_Question
                                                                    uu___12
                                                                    (fun
                                                                    _f_b_ok_
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    let expected_g_b_sort
                                                                    =
                                                                    let x_bv
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    a_b.FStar_Syntax_Syntax.binder_bv
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "x"
                                                                    FStar_Pervasives_Native.None
                                                                    uu___14 in
                                                                    let repr_args
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStar_Compiler_List.map2
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    fun kind
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = b;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___16;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___17;_}
                                                                    ->
                                                                    if
                                                                    kind =
                                                                    FStar_Syntax_Syntax.Substitution_binder
                                                                    then
                                                                    let uu___18
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    b
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    x_bv
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___21
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                    [uu___20] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu___18
                                                                    uu___19
                                                                    FStar_Compiler_Range.dummyRange
                                                                    else
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    b
                                                                    FStar_Syntax_Syntax.bv_to_name)
                                                                    g_bs
                                                                    g_bs_kinds in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___14
                                                                    (FStar_Compiler_List.map
                                                                    FStar_Syntax_Syntax.as_arg) in
                                                                    match n_repr_ts
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    repr_ts
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme_with
                                                                    repr_ts
                                                                    [
                                                                    FStar_Syntax_Syntax.U_name
                                                                    u_b] in
                                                                    (match uu___14
                                                                    with
                                                                    | 
                                                                    (uu___15,
                                                                    repr_hd)
                                                                    ->
                                                                    let repr_app
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    b_b.FStar_Syntax_Syntax.binder_bv
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___18
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                    uu___17
                                                                    ::
                                                                    repr_args in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    repr_hd
                                                                    uu___16
                                                                    FStar_Compiler_Range.dummyRange in
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    x_bv
                                                                    FStar_Syntax_Syntax.mk_binder in
                                                                    [uu___17] in
                                                                    let uu___17
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    repr_app in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu___16
                                                                    uu___17)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let thunk_t
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    [uu___15] in
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    b_b.FStar_Syntax_Syntax.binder_bv
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    [
                                                                    FStar_Syntax_Syntax.U_name
                                                                    u_b];
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    n_eff_name;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = uu___17;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    repr_args;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    uu___16 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu___14
                                                                    uu___15 in
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    x_bv
                                                                    FStar_Syntax_Syntax.mk_binder in
                                                                    [uu___15] in
                                                                    let uu___15
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    thunk_t in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu___14
                                                                    uu___15 in
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Syntax_Util.eq_tm
                                                                    (g_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                                                    expected_g_b_sort in
                                                                    uu___15 =
                                                                    FStar_Syntax_Util.Equal in
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
                                                                    _g_b_ok
                                                                    ->
                                                                    let range_kinds
                                                                    =
                                                                    FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Syntax_Syntax.Range_binder)
                                                                    range_bs in
                                                                    let rest_kinds
                                                                    =
                                                                    FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Syntax_Syntax.Ad_hoc_binder)
                                                                    rest_bs4 in
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Compiler_List.op_At
                                                                    [FStar_Syntax_Syntax.Type_binder;
                                                                    FStar_Syntax_Syntax.Type_binder]
                                                                    (FStar_Compiler_List.op_At
                                                                    f_bs_kinds
                                                                    (FStar_Compiler_List.op_At
                                                                    g_bs_kinds
                                                                    (FStar_Compiler_List.op_At
                                                                    range_kinds
                                                                    (FStar_Compiler_List.op_At
                                                                    rest_kinds
                                                                    [FStar_Syntax_Syntax.Repr_binder;
                                                                    FStar_Syntax_Syntax.Repr_binder])))))))))))))
let (validate_indexed_effect_bind_shape :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme ->
            FStar_Syntax_Syntax.tscheme ->
              FStar_Syntax_Syntax.tscheme ->
                FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ->
                  FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option
                    ->
                    FStar_Syntax_Syntax.tscheme
                      FStar_Pervasives_Native.option ->
                      FStar_Syntax_Syntax.univ_names ->
                        FStar_Syntax_Syntax.typ ->
                          FStar_Compiler_Range.range ->
                            Prims.bool ->
                              (FStar_Syntax_Syntax.typ *
                                FStar_Syntax_Syntax.indexed_effect_combinator_kind))
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
                            fun has_range_binders ->
                              let bind_name =
                                let uu___ =
                                  FStar_Ident.string_of_lid m_eff_name in
                                let uu___1 =
                                  FStar_Ident.string_of_lid n_eff_name in
                                let uu___2 =
                                  FStar_Ident.string_of_lid p_eff_name in
                                FStar_Compiler_Util.format3 "(%s , %s) |> %s"
                                  uu___ uu___1 uu___2 in
                              let uu___ = bind_us in
                              match uu___ with
                              | u_a::u_b::[] ->
                                  let a_b =
                                    let uu___1 =
                                      let uu___2 =
                                        FStar_Compiler_Effect.op_Bar_Greater
                                          (FStar_Syntax_Syntax.U_name u_a)
                                          FStar_Syntax_Util.type_with_u in
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        uu___2
                                        (FStar_Syntax_Syntax.gen_bv "a"
                                           FStar_Pervasives_Native.None) in
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      uu___1 FStar_Syntax_Syntax.mk_binder in
                                  let b_b =
                                    let uu___1 =
                                      let uu___2 =
                                        FStar_Compiler_Effect.op_Bar_Greater
                                          (FStar_Syntax_Syntax.U_name u_b)
                                          FStar_Syntax_Util.type_with_u in
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        uu___2
                                        (FStar_Syntax_Syntax.gen_bv "b"
                                           FStar_Pervasives_Native.None) in
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      uu___1 FStar_Syntax_Syntax.mk_binder in
                                  let rest_bs =
                                    let uu___1 =
                                      let uu___2 =
                                        FStar_Syntax_Subst.compress bind_t in
                                      uu___2.FStar_Syntax_Syntax.n in
                                    match uu___1 with
                                    | FStar_Syntax_Syntax.Tm_arrow
                                        (bs, uu___2) when
                                        (FStar_Compiler_List.length bs) >=
                                          (Prims.of_int (4))
                                        ->
                                        let uu___3 =
                                          FStar_Syntax_Subst.open_binders bs in
                                        (match uu___3 with
                                         | {
                                             FStar_Syntax_Syntax.binder_bv =
                                               a;
                                             FStar_Syntax_Syntax.binder_qual
                                               = uu___4;
                                             FStar_Syntax_Syntax.binder_attrs
                                               = uu___5;_}::{
                                                              FStar_Syntax_Syntax.binder_bv
                                                                = b;
                                                              FStar_Syntax_Syntax.binder_qual
                                                                = uu___6;
                                                              FStar_Syntax_Syntax.binder_attrs
                                                                = uu___7;_}::bs1
                                             ->
                                             let uu___8 =
                                               let uu___9 =
                                                 FStar_Compiler_Effect.op_Bar_Greater
                                                   bs1
                                                   (FStar_Compiler_List.splitAt
                                                      ((FStar_Compiler_List.length
                                                          bs1)
                                                         - (Prims.of_int (2)))) in
                                               FStar_Compiler_Effect.op_Bar_Greater
                                                 uu___9
                                                 FStar_Pervasives_Native.fst in
                                             let uu___9 =
                                               let uu___10 =
                                                 let uu___11 =
                                                   let uu___12 =
                                                     let uu___13 =
                                                       FStar_Compiler_Effect.op_Bar_Greater
                                                         a_b.FStar_Syntax_Syntax.binder_bv
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     (a, uu___13) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu___12 in
                                                 let uu___12 =
                                                   let uu___13 =
                                                     let uu___14 =
                                                       let uu___15 =
                                                         FStar_Compiler_Effect.op_Bar_Greater
                                                           b_b.FStar_Syntax_Syntax.binder_bv
                                                           FStar_Syntax_Syntax.bv_to_name in
                                                       (b, uu___15) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu___14 in
                                                   [uu___13] in
                                                 uu___11 :: uu___12 in
                                               FStar_Syntax_Subst.subst_binders
                                                 uu___10 in
                                             FStar_Compiler_Effect.op_Bar_Greater
                                               uu___8 uu___9)
                                    | uu___2 ->
                                        let uu___3 =
                                          let uu___4 =
                                            let uu___5 =
                                              FStar_Syntax_Print.term_to_string
                                                bind_t in
                                            FStar_Compiler_Util.format2
                                              "Type of %s is not an arrow with >= 4 binders (%s)"
                                              bind_name uu___5 in
                                          (FStar_Errors.Fatal_UnexpectedEffect,
                                            uu___4) in
                                        FStar_Errors.raise_error uu___3 r in
                                  let uu___1 =
                                    if has_range_binders
                                    then
                                      (if
                                         (FStar_Compiler_List.length rest_bs)
                                           >= (Prims.of_int (2))
                                       then
                                         FStar_Compiler_List.splitAt
                                           ((FStar_Compiler_List.length
                                               rest_bs)
                                              - (Prims.of_int (2))) rest_bs
                                       else
                                         (let uu___3 =
                                            let uu___4 =
                                              let uu___5 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t in
                                              FStar_Compiler_Util.format2
                                                "Type of %s is not an arrow with >= 6 binders (%s)"
                                                bind_name uu___5 in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu___4) in
                                          FStar_Errors.raise_error uu___3 r))
                                    else (rest_bs, []) in
                                  (match uu___1 with
                                   | (rest_bs1, range_bs) ->
                                       let uu___2 =
                                         let uu___3 =
                                           let uu___4 =
                                             FStar_TypeChecker_Env.push_binders
                                               env (a_b :: b_b :: rest_bs1) in
                                           let uu___5 =
                                             FStar_Compiler_Effect.op_Bar_Greater
                                               a_b.FStar_Syntax_Syntax.binder_bv
                                               FStar_Syntax_Syntax.bv_to_name in
                                           FStar_TypeChecker_Util.fresh_effect_repr
                                             uu___4 r m_eff_name m_sig_ts
                                             m_repr_ts
                                             (FStar_Syntax_Syntax.U_name u_a)
                                             uu___5 in
                                         match uu___3 with
                                         | (repr, g) ->
                                             let uu___4 =
                                               let uu___5 =
                                                 FStar_Compiler_Effect.op_Bar_Greater
                                                   repr
                                                   (FStar_Syntax_Syntax.gen_bv
                                                      "f"
                                                      FStar_Pervasives_Native.None) in
                                               FStar_Compiler_Effect.op_Bar_Greater
                                                 uu___5
                                                 FStar_Syntax_Syntax.mk_binder in
                                             (uu___4, g) in
                                       (match uu___2 with
                                        | (f, guard_f) ->
                                            let uu___3 =
                                              let x_a =
                                                let uu___4 =
                                                  let uu___5 =
                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                      a_b.FStar_Syntax_Syntax.binder_bv
                                                      FStar_Syntax_Syntax.bv_to_name in
                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                    uu___5
                                                    (FStar_Syntax_Syntax.gen_bv
                                                       "x"
                                                       FStar_Pervasives_Native.None) in
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  uu___4
                                                  FStar_Syntax_Syntax.mk_binder in
                                              let uu___4 =
                                                let uu___5 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_Compiler_List.op_At
                                                       (a_b :: b_b ::
                                                       rest_bs1) [x_a]) in
                                                let uu___6 =
                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                    b_b.FStar_Syntax_Syntax.binder_bv
                                                    FStar_Syntax_Syntax.bv_to_name in
                                                FStar_TypeChecker_Util.fresh_effect_repr
                                                  uu___5 r n_eff_name
                                                  n_sig_ts n_repr_ts
                                                  (FStar_Syntax_Syntax.U_name
                                                     u_b) uu___6 in
                                              match uu___4 with
                                              | (repr, g) ->
                                                  let uu___5 =
                                                    let uu___6 =
                                                      let uu___7 =
                                                        let uu___8 =
                                                          let uu___9 =
                                                            let uu___10 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                () in
                                                            FStar_Pervasives_Native.Some
                                                              uu___10 in
                                                          FStar_Syntax_Syntax.mk_Total'
                                                            repr uu___9 in
                                                        FStar_Syntax_Util.arrow
                                                          [x_a] uu___8 in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "g"
                                                        FStar_Pervasives_Native.None
                                                        uu___7 in
                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                      uu___6
                                                      FStar_Syntax_Syntax.mk_binder in
                                                  (uu___5, g) in
                                            (match uu___3 with
                                             | (g, guard_g) ->
                                                 let uu___4 =
                                                   let uu___5 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env (a_b :: b_b ::
                                                       rest_bs1) in
                                                   let uu___6 =
                                                     FStar_Compiler_Effect.op_Bar_Greater
                                                       b_b.FStar_Syntax_Syntax.binder_bv
                                                       FStar_Syntax_Syntax.bv_to_name in
                                                   FStar_TypeChecker_Util.fresh_effect_repr
                                                     uu___5 r p_eff_name
                                                     p_sig_ts p_repr_ts
                                                     (FStar_Syntax_Syntax.U_name
                                                        u_b) uu___6 in
                                                 (match uu___4 with
                                                  | (return_repr,
                                                     guard_return_repr) ->
                                                      let uu___5 =
                                                        let uu___6 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env (a_b :: b_b
                                                            :: rest_bs1) in
                                                        let uu___7 =
                                                          FStar_Compiler_Util.format1
                                                            "implicit for pure_wp in checking bind %s"
                                                            bind_name in
                                                        pure_wp_uvar uu___6
                                                          return_repr uu___7
                                                          r in
                                                      (match uu___5 with
                                                       | (pure_wp_uvar1,
                                                          g_pure_wp_uvar) ->
                                                           let k =
                                                             let uu___6 =
                                                               let uu___7 =
                                                                 let uu___8 =
                                                                   let uu___9
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    () in
                                                                   [uu___9] in
                                                                 let uu___9 =
                                                                   let uu___10
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                   [uu___10] in
                                                                 {
                                                                   FStar_Syntax_Syntax.comp_univs
                                                                    = uu___8;
                                                                   FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                   FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    return_repr;
                                                                   FStar_Syntax_Syntax.effect_args
                                                                    = uu___9;
                                                                   FStar_Syntax_Syntax.flags
                                                                    = []
                                                                 } in
                                                               FStar_Syntax_Syntax.mk_Comp
                                                                 uu___7 in
                                                             FStar_Syntax_Util.arrow
                                                               (a_b :: b_b ::
                                                               (FStar_Compiler_List.op_At
                                                                  rest_bs1
                                                                  (FStar_Compiler_List.op_At
                                                                    range_bs
                                                                    [f; g])))
                                                               uu___6 in
                                                           let guard_eq =
                                                             let uu___6 =
                                                               FStar_TypeChecker_Rel.teq_nosmt
                                                                 env k bind_t in
                                                             match uu___6
                                                             with
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 let uu___7 =
                                                                   let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t in
                                                                    FStar_Compiler_Util.format2
                                                                    "Unexpected type of %s (%s)\n"
                                                                    bind_name
                                                                    uu___9 in
                                                                   (FStar_Errors.Fatal_UnexpectedEffect,
                                                                    uu___8) in
                                                                 FStar_Errors.raise_error
                                                                   uu___7 r
                                                             | FStar_Pervasives_Native.Some
                                                                 g1 -> g1 in
                                                           ((let uu___7 =
                                                               FStar_TypeChecker_Env.conj_guards
                                                                 [guard_f;
                                                                 guard_g;
                                                                 guard_return_repr;
                                                                 g_pure_wp_uvar;
                                                                 guard_eq] in
                                                             FStar_TypeChecker_Rel.force_trivial_guard
                                                               env uu___7);
                                                            (let k1 =
                                                               let uu___7 =
                                                                 FStar_Compiler_Effect.op_Bar_Greater
                                                                   k
                                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                    env) in
                                                               FStar_Compiler_Effect.op_Bar_Greater
                                                                 uu___7
                                                                 FStar_Syntax_Subst.compress in
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
                                                                 has_range_binders in
                                                             let kind =
                                                               match lopt
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                   ->
                                                                   FStar_Syntax_Syntax.Ad_hoc_combinator
                                                               | FStar_Pervasives_Native.Some
                                                                   l ->
                                                                   FStar_Syntax_Syntax.Standard_combinator
                                                                    l in
                                                             (let uu___8 =
                                                                FStar_Compiler_Effect.op_Less_Bar
                                                                  (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                  (FStar_Options.Other
                                                                    "LayeredEffectsTc") in
                                                              if uu___8
                                                              then
                                                                let uu___9 =
                                                                  FStar_Syntax_Print.indexed_effect_combinator_kind_to_string
                                                                    kind in
                                                                FStar_Compiler_Util.print2
                                                                  "Bind %s has %s kind\n"
                                                                  bind_name
                                                                  uu___9
                                                              else ());
                                                             (k1, kind))))))))
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun env0 ->
    fun ed ->
      fun quals ->
        fun attrs ->
          let uu___ =
            let uu___1 =
              FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
            FStar_Compiler_Util.format1
              "While checking layered effect definition `%s`" uu___1 in
          FStar_Errors.with_ctx uu___
            (fun uu___1 ->
               (let uu___3 =
                  FStar_Compiler_Effect.op_Less_Bar
                    (FStar_TypeChecker_Env.debug env0)
                    (FStar_Options.Other "LayeredEffectsTc") in
                if uu___3
                then
                  let uu___4 = FStar_Syntax_Print.eff_decl_to_string false ed in
                  FStar_Compiler_Util.print1
                    "Typechecking layered effect: \n\t%s\n" uu___4
                else ());
               if
                 ((FStar_Compiler_List.length ed.FStar_Syntax_Syntax.univs)
                    <> Prims.int_zero)
                   ||
                   ((FStar_Compiler_List.length
                       ed.FStar_Syntax_Syntax.binders)
                      <> Prims.int_zero)
               then
                 (let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          FStar_Ident.string_of_lid
                            ed.FStar_Syntax_Syntax.mname in
                        Prims.op_Hat uu___7 ")" in
                      Prims.op_Hat
                        "Binders are not supported for layered effects ("
                        uu___6 in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu___5) in
                  let uu___5 =
                    FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname in
                  FStar_Errors.raise_error uu___4 uu___5)
               else ();
               (let log_combinator s uu___4 =
                  match uu___4 with
                  | (us, t, ty) ->
                      let uu___5 =
                        FStar_Compiler_Effect.op_Less_Bar
                          (FStar_TypeChecker_Env.debug env0)
                          (FStar_Options.Other "LayeredEffectsTc") in
                      if uu___5
                      then
                        let uu___6 =
                          FStar_Ident.string_of_lid
                            ed.FStar_Syntax_Syntax.mname in
                        let uu___7 =
                          FStar_Syntax_Print.tscheme_to_string (us, t) in
                        let uu___8 =
                          FStar_Syntax_Print.tscheme_to_string (us, ty) in
                        FStar_Compiler_Util.print4
                          "Typechecked %s:%s = %s:%s\n" uu___6 s uu___7
                          uu___8
                      else () in
                let fresh_a_and_u_a a =
                  let uu___4 = FStar_Syntax_Util.type_u () in
                  FStar_Compiler_Effect.op_Bar_Greater uu___4
                    (fun uu___5 ->
                       match uu___5 with
                       | (t, u) ->
                           let uu___6 =
                             let uu___7 =
                               FStar_Syntax_Syntax.gen_bv a
                                 FStar_Pervasives_Native.None t in
                             FStar_Compiler_Effect.op_Bar_Greater uu___7
                               FStar_Syntax_Syntax.mk_binder in
                           (uu___6, u)) in
                let fresh_x_a x a =
                  let uu___4 =
                    let uu___5 =
                      FStar_Syntax_Syntax.bv_to_name
                        a.FStar_Syntax_Syntax.binder_bv in
                    FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
                      uu___5 in
                  FStar_Compiler_Effect.op_Bar_Greater uu___4
                    FStar_Syntax_Syntax.mk_binder in
                let check_and_gen1 =
                  let uu___4 =
                    FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                  check_and_gen env0 uu___4 in
                let signature =
                  let r =
                    (FStar_Pervasives_Native.snd
                       ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                  let uu___4 =
                    check_and_gen1 "signature" Prims.int_one
                      ed.FStar_Syntax_Syntax.signature in
                  match uu___4 with
                  | (sig_us, sig_t, sig_ty) ->
                      let uu___5 =
                        FStar_Syntax_Subst.open_univ_vars sig_us sig_t in
                      (match uu___5 with
                       | (us, t) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us in
                           let uu___6 = fresh_a_and_u_a "a" in
                           (match uu___6 with
                            | (a, u) ->
                                let rest_bs =
                                  let uu___7 =
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      a.FStar_Syntax_Syntax.binder_bv
                                      FStar_Syntax_Syntax.bv_to_name in
                                  FStar_TypeChecker_Util.layered_effect_indices_as_binders
                                    env r ed.FStar_Syntax_Syntax.mname
                                    (sig_us, sig_t) u uu___7 in
                                let bs = a :: rest_bs in
                                let k =
                                  let uu___7 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Syntax.teff in
                                  FStar_Syntax_Util.arrow bs uu___7 in
                                let g_eq = FStar_TypeChecker_Rel.teq env t k in
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env g_eq;
                                 (let uu___8 =
                                    let uu___9 =
                                      FStar_Compiler_Effect.op_Bar_Greater k
                                        (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                           env) in
                                    FStar_Syntax_Subst.close_univ_vars us
                                      uu___9 in
                                  (sig_us, uu___8, sig_ty))))) in
                log_combinator "signature" signature;
                (let repr =
                   let repr_ts =
                     let uu___5 =
                       FStar_Compiler_Effect.op_Bar_Greater ed
                         FStar_Syntax_Util.get_eff_repr in
                     FStar_Compiler_Effect.op_Bar_Greater uu___5
                       FStar_Compiler_Util.must in
                   let r =
                     (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos in
                   let uu___5 = check_and_gen1 "repr" Prims.int_one repr_ts in
                   match uu___5 with
                   | (repr_us, repr_t, repr_ty) ->
                       let uu___6 =
                         FStar_Syntax_Subst.open_univ_vars repr_us repr_ty in
                       (match uu___6 with
                        | (us, ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us in
                            let uu___7 = fresh_a_and_u_a "a" in
                            (match uu___7 with
                             | (a, u) ->
                                 let rest_bs =
                                   let signature_ts =
                                     let uu___8 = signature in
                                     match uu___8 with
                                     | (us1, t, uu___9) -> (us1, t) in
                                   let uu___8 =
                                     FStar_Compiler_Effect.op_Bar_Greater
                                       a.FStar_Syntax_Syntax.binder_bv
                                       FStar_Syntax_Syntax.bv_to_name in
                                   FStar_TypeChecker_Util.layered_effect_indices_as_binders
                                     env r ed.FStar_Syntax_Syntax.mname
                                     signature_ts u uu___8 in
                                 let bs = a :: rest_bs in
                                 let k =
                                   let uu___8 =
                                     let uu___9 = FStar_Syntax_Util.type_u () in
                                     FStar_Compiler_Effect.op_Bar_Greater
                                       uu___9
                                       (fun uu___10 ->
                                          match uu___10 with
                                          | (t, u1) ->
                                              let uu___11 =
                                                let uu___12 =
                                                  FStar_TypeChecker_Env.new_u_univ
                                                    () in
                                                FStar_Pervasives_Native.Some
                                                  uu___12 in
                                              FStar_Syntax_Syntax.mk_Total' t
                                                uu___11) in
                                   FStar_Syntax_Util.arrow bs uu___8 in
                                 let g = FStar_TypeChecker_Rel.teq env ty k in
                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                    env g;
                                  (let uu___9 =
                                     let uu___10 =
                                       FStar_Compiler_Effect.op_Bar_Greater k
                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                            env) in
                                     FStar_Syntax_Subst.close_univ_vars us
                                       uu___10 in
                                   (repr_us, repr_t, uu___9))))) in
                 log_combinator "repr" repr;
                 (let fresh_repr r env u a_tm =
                    let signature_ts =
                      let uu___6 = signature in
                      match uu___6 with | (us, t, uu___7) -> (us, t) in
                    let repr_ts =
                      let uu___6 = repr in
                      match uu___6 with | (us, t, uu___7) -> (us, t) in
                    FStar_TypeChecker_Util.fresh_effect_repr env r
                      ed.FStar_Syntax_Syntax.mname signature_ts
                      (FStar_Pervasives_Native.Some repr_ts) u a_tm in
                  let not_an_arrow_error comb n t r =
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          FStar_Ident.string_of_lid
                            ed.FStar_Syntax_Syntax.mname in
                        let uu___9 = FStar_Compiler_Util.string_of_int n in
                        let uu___10 = FStar_Syntax_Print.tag_of_term t in
                        let uu___11 = FStar_Syntax_Print.term_to_string t in
                        FStar_Compiler_Util.format5
                          "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                          uu___8 comb uu___9 uu___10 uu___11 in
                      (FStar_Errors.Fatal_UnexpectedEffect, uu___7) in
                    FStar_Errors.raise_error uu___6 r in
                  let check_non_informative_binders =
                    (FStar_Compiler_List.contains
                       FStar_Syntax_Syntax.Reifiable quals)
                      &&
                      (let uu___6 =
                         FStar_Syntax_Util.has_attribute attrs
                           FStar_Parser_Const.allow_informative_binders_attr in
                       Prims.op_Negation uu___6) in
                  let return_repr =
                    let return_repr_ts =
                      let uu___6 =
                        FStar_Compiler_Effect.op_Bar_Greater ed
                          FStar_Syntax_Util.get_return_repr in
                      FStar_Compiler_Effect.op_Bar_Greater uu___6
                        FStar_Compiler_Util.must in
                    let r =
                      (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos in
                    let uu___6 =
                      check_and_gen1 "return_repr" Prims.int_one
                        return_repr_ts in
                    match uu___6 with
                    | (ret_us, ret_t, ret_ty) ->
                        let uu___7 =
                          FStar_Syntax_Subst.open_univ_vars ret_us ret_ty in
                        (match uu___7 with
                         | (us, ty) ->
                             let env =
                               FStar_TypeChecker_Env.push_univ_vars env0 us in
                             let uu___9 = fresh_a_and_u_a "a" in
                             (match uu___9 with
                              | (a, u_a) ->
                                  let x_a = fresh_x_a "x" a in
                                  let rest_bs =
                                    let uu___10 =
                                      let uu___11 =
                                        FStar_Syntax_Subst.compress ty in
                                      uu___11.FStar_Syntax_Syntax.n in
                                    match uu___10 with
                                    | FStar_Syntax_Syntax.Tm_arrow
                                        (bs, uu___11) when
                                        (FStar_Compiler_List.length bs) >=
                                          (Prims.of_int (2))
                                        ->
                                        let uu___12 =
                                          FStar_Syntax_Subst.open_binders bs in
                                        (match uu___12 with
                                         | {
                                             FStar_Syntax_Syntax.binder_bv =
                                               a';
                                             FStar_Syntax_Syntax.binder_qual
                                               = uu___13;
                                             FStar_Syntax_Syntax.binder_attrs
                                               = uu___14;_}::{
                                                               FStar_Syntax_Syntax.binder_bv
                                                                 = x';
                                                               FStar_Syntax_Syntax.binder_qual
                                                                 = uu___15;
                                                               FStar_Syntax_Syntax.binder_attrs
                                                                 = uu___16;_}::bs1
                                             ->
                                             let uu___17 =
                                               let uu___18 =
                                                 let uu___19 =
                                                   let uu___20 =
                                                     let uu___21 =
                                                       let uu___22 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a.FStar_Syntax_Syntax.binder_bv in
                                                       (a', uu___22) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu___21 in
                                                   [uu___20] in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu___19 in
                                               FStar_Compiler_Effect.op_Bar_Greater
                                                 bs1 uu___18 in
                                             let uu___18 =
                                               let uu___19 =
                                                 let uu___20 =
                                                   let uu___21 =
                                                     let uu___22 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a.FStar_Syntax_Syntax.binder_bv in
                                                     (x', uu___22) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu___21 in
                                                 [uu___20] in
                                               FStar_Syntax_Subst.subst_binders
                                                 uu___19 in
                                             FStar_Compiler_Effect.op_Bar_Greater
                                               uu___17 uu___18)
                                    | uu___11 ->
                                        not_an_arrow_error "return"
                                          (Prims.of_int (2)) ty r in
                                  let bs = a :: x_a :: rest_bs in
                                  let uu___10 =
                                    let uu___11 =
                                      FStar_TypeChecker_Env.push_binders env
                                        bs in
                                    let uu___12 =
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        a.FStar_Syntax_Syntax.binder_bv
                                        FStar_Syntax_Syntax.bv_to_name in
                                    fresh_repr r uu___11 u_a uu___12 in
                                  (match uu___10 with
                                   | (repr1, g) ->
                                       let k =
                                         let uu___11 =
                                           FStar_Syntax_Syntax.mk_Total'
                                             repr1
                                             (FStar_Pervasives_Native.Some
                                                u_a) in
                                         FStar_Syntax_Util.arrow bs uu___11 in
                                       let g_eq =
                                         FStar_TypeChecker_Rel.teq env ty k in
                                       ((let uu___12 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_eq in
                                         FStar_TypeChecker_Rel.force_trivial_guard
                                           env uu___12);
                                        (let k1 =
                                           FStar_Compiler_Effect.op_Bar_Greater
                                             k
                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                env) in
                                         (let uu___12 =
                                            let uu___13 =
                                              FStar_Syntax_Subst.compress k1 in
                                            uu___13.FStar_Syntax_Syntax.n in
                                          match uu___12 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs1, c) ->
                                              let uu___13 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs1 c in
                                              (match uu___13 with
                                               | (a1::x::bs2, c1) ->
                                                   let res_t =
                                                     FStar_Syntax_Util.comp_result
                                                       c1 in
                                                   let env1 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env [a1; x] in
                                                   validate_layered_effect_binders
                                                     env1 bs2
                                                     check_non_informative_binders
                                                     r));
                                         (let uu___12 =
                                            FStar_Compiler_Effect.op_Bar_Greater
                                              k1
                                              (FStar_Syntax_Subst.close_univ_vars
                                                 us) in
                                          (ret_us, ret_t, uu___12))))))) in
                  log_combinator "return_repr" return_repr;
                  (let uu___7 =
                     let bind_repr_ts =
                       let uu___8 =
                         FStar_Compiler_Effect.op_Bar_Greater ed
                           FStar_Syntax_Util.get_bind_repr in
                       FStar_Compiler_Effect.op_Bar_Greater uu___8
                         FStar_Compiler_Util.must in
                     let r =
                       (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos in
                     let uu___8 =
                       check_and_gen1 "bind_repr" (Prims.of_int (2))
                         bind_repr_ts in
                     match uu___8 with
                     | (bind_us, bind_t, bind_ty) ->
                         let uu___9 =
                           FStar_Syntax_Subst.open_univ_vars bind_us bind_ty in
                         (match uu___9 with
                          | (us, ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us in
                              let uu___10 =
                                let sig_ts =
                                  let uu___11 = signature in
                                  match uu___11 with
                                  | (us1, t, uu___12) -> (us1, t) in
                                let repr_ts =
                                  let uu___11 = repr in
                                  match uu___11 with
                                  | (us1, t, uu___12) -> (us1, t) in
                                let uu___11 =
                                  FStar_Syntax_Util.has_attribute
                                    ed.FStar_Syntax_Syntax.eff_attrs
                                    FStar_Parser_Const.bind_has_range_args_attr in
                                validate_indexed_effect_bind_shape env
                                  ed.FStar_Syntax_Syntax.mname
                                  ed.FStar_Syntax_Syntax.mname
                                  ed.FStar_Syntax_Syntax.mname sig_ts sig_ts
                                  sig_ts
                                  (FStar_Pervasives_Native.Some repr_ts)
                                  (FStar_Pervasives_Native.Some repr_ts)
                                  (FStar_Pervasives_Native.Some repr_ts) us
                                  ty r uu___11 in
                              (match uu___10 with
                               | (k, kind) ->
                                   let uu___11 =
                                     let uu___12 =
                                       FStar_Compiler_Effect.op_Bar_Greater k
                                         (FStar_Syntax_Subst.close_univ_vars
                                            bind_us) in
                                     (bind_us, bind_t, uu___12) in
                                   (uu___11, kind))) in
                   match uu___7 with
                   | (bind_repr, bind_combinator_kind1) ->
                       (log_combinator "bind_repr" bind_repr;
                        (let stronger_repr =
                           let stronger_repr1 =
                             let ts =
                               let uu___9 =
                                 FStar_Compiler_Effect.op_Bar_Greater ed
                                   FStar_Syntax_Util.get_stronger_repr in
                               FStar_Compiler_Effect.op_Bar_Greater uu___9
                                 FStar_Compiler_Util.must in
                             let uu___9 =
                               let uu___10 =
                                 let uu___11 =
                                   FStar_Compiler_Effect.op_Bar_Greater ts
                                     FStar_Pervasives_Native.snd in
                                 FStar_Compiler_Effect.op_Bar_Greater uu___11
                                   FStar_Syntax_Subst.compress in
                               uu___10.FStar_Syntax_Syntax.n in
                             match uu___9 with
                             | FStar_Syntax_Syntax.Tm_unknown ->
                                 let signature_ts =
                                   let uu___10 = signature in
                                   match uu___10 with
                                   | (us, t, uu___11) -> (us, t) in
                                 let uu___10 =
                                   FStar_TypeChecker_Env.inst_tscheme_with
                                     signature_ts
                                     [FStar_Syntax_Syntax.U_unknown] in
                                 (match uu___10 with
                                  | (uu___11, signature_t) ->
                                      let uu___12 =
                                        let uu___13 =
                                          FStar_Syntax_Subst.compress
                                            signature_t in
                                        uu___13.FStar_Syntax_Syntax.n in
                                      (match uu___12 with
                                       | FStar_Syntax_Syntax.Tm_arrow
                                           (bs, uu___13) ->
                                           let bs1 =
                                             FStar_Syntax_Subst.open_binders
                                               bs in
                                           let repr_t =
                                             let repr_ts =
                                               let uu___14 = repr in
                                               match uu___14 with
                                               | (us, t, uu___15) -> (us, t) in
                                             let uu___14 =
                                               FStar_TypeChecker_Env.inst_tscheme_with
                                                 repr_ts
                                                 [FStar_Syntax_Syntax.U_unknown] in
                                             FStar_Compiler_Effect.op_Bar_Greater
                                               uu___14
                                               FStar_Pervasives_Native.snd in
                                           let repr_t_applied =
                                             let uu___14 =
                                               let uu___15 =
                                                 let uu___16 =
                                                   let uu___17 =
                                                     let uu___18 =
                                                       FStar_Compiler_Effect.op_Bar_Greater
                                                         bs1
                                                         (FStar_Compiler_List.map
                                                            (fun b ->
                                                               b.FStar_Syntax_Syntax.binder_bv)) in
                                                     FStar_Compiler_Effect.op_Bar_Greater
                                                       uu___18
                                                       (FStar_Compiler_List.map
                                                          FStar_Syntax_Syntax.bv_to_name) in
                                                   FStar_Compiler_Effect.op_Bar_Greater
                                                     uu___17
                                                     (FStar_Compiler_List.map
                                                        FStar_Syntax_Syntax.as_arg) in
                                                 (repr_t, uu___16) in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu___15 in
                                             FStar_Syntax_Syntax.mk uu___14
                                               FStar_Compiler_Range.dummyRange in
                                           let f_b =
                                             FStar_Syntax_Syntax.null_binder
                                               repr_t_applied in
                                           let uu___14 =
                                             let uu___15 =
                                               FStar_Compiler_Effect.op_Bar_Greater
                                                 f_b.FStar_Syntax_Syntax.binder_bv
                                                 FStar_Syntax_Syntax.bv_to_name in
                                             FStar_Syntax_Util.abs
                                               (FStar_Compiler_List.op_At bs1
                                                  [f_b]) uu___15
                                               FStar_Pervasives_Native.None in
                                           ([], uu___14)
                                       | uu___13 -> failwith "Impossible!"))
                             | uu___10 -> ts in
                           let r =
                             (FStar_Pervasives_Native.snd stronger_repr1).FStar_Syntax_Syntax.pos in
                           let uu___9 =
                             check_and_gen1 "stronger_repr" Prims.int_one
                               stronger_repr1 in
                           match uu___9 with
                           | (stronger_us, stronger_t, stronger_ty) ->
                               ((let uu___11 =
                                   FStar_Compiler_Effect.op_Less_Bar
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "LayeredEffectsTc") in
                                 if uu___11
                                 then
                                   let uu___12 =
                                     FStar_Syntax_Print.tscheme_to_string
                                       (stronger_us, stronger_t) in
                                   let uu___13 =
                                     FStar_Syntax_Print.tscheme_to_string
                                       (stronger_us, stronger_ty) in
                                   FStar_Compiler_Util.print2
                                     "stronger combinator typechecked with term: %s and type: %s\n"
                                     uu___12 uu___13
                                 else ());
                                (let uu___11 =
                                   FStar_Syntax_Subst.open_univ_vars
                                     stronger_us stronger_ty in
                                 match uu___11 with
                                 | (us, ty) ->
                                     let env =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us in
                                     let uu___13 = fresh_a_and_u_a "a" in
                                     (match uu___13 with
                                      | (a, u) ->
                                          let rest_bs =
                                            let uu___14 =
                                              let uu___15 =
                                                FStar_Syntax_Subst.compress
                                                  ty in
                                              uu___15.FStar_Syntax_Syntax.n in
                                            match uu___14 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs, uu___15) when
                                                (FStar_Compiler_List.length
                                                   bs)
                                                  >= (Prims.of_int (2))
                                                ->
                                                let uu___16 =
                                                  FStar_Syntax_Subst.open_binders
                                                    bs in
                                                (match uu___16 with
                                                 | {
                                                     FStar_Syntax_Syntax.binder_bv
                                                       = a';
                                                     FStar_Syntax_Syntax.binder_qual
                                                       = uu___17;
                                                     FStar_Syntax_Syntax.binder_attrs
                                                       = uu___18;_}::bs1
                                                     ->
                                                     let uu___19 =
                                                       let uu___20 =
                                                         FStar_Compiler_Effect.op_Bar_Greater
                                                           bs1
                                                           (FStar_Compiler_List.splitAt
                                                              ((FStar_Compiler_List.length
                                                                  bs1)
                                                                 -
                                                                 Prims.int_one)) in
                                                       FStar_Compiler_Effect.op_Bar_Greater
                                                         uu___20
                                                         FStar_Pervasives_Native.fst in
                                                     let uu___20 =
                                                       let uu___21 =
                                                         let uu___22 =
                                                           let uu___23 =
                                                             let uu___24 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 a.FStar_Syntax_Syntax.binder_bv in
                                                             (a', uu___24) in
                                                           FStar_Syntax_Syntax.NT
                                                             uu___23 in
                                                         [uu___22] in
                                                       FStar_Syntax_Subst.subst_binders
                                                         uu___21 in
                                                     FStar_Compiler_Effect.op_Bar_Greater
                                                       uu___19 uu___20)
                                            | uu___15 ->
                                                not_an_arrow_error "stronger"
                                                  (Prims.of_int (2)) ty r in
                                          let bs = a :: rest_bs in
                                          let uu___14 =
                                            let uu___15 =
                                              let uu___16 =
                                                FStar_TypeChecker_Env.push_binders
                                                  env bs in
                                              let uu___17 =
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  a.FStar_Syntax_Syntax.binder_bv
                                                  FStar_Syntax_Syntax.bv_to_name in
                                              fresh_repr r uu___16 u uu___17 in
                                            match uu___15 with
                                            | (repr1, g) ->
                                                let uu___16 =
                                                  let uu___17 =
                                                    FStar_Syntax_Syntax.gen_bv
                                                      "f"
                                                      FStar_Pervasives_Native.None
                                                      repr1 in
                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                    uu___17
                                                    FStar_Syntax_Syntax.mk_binder in
                                                (uu___16, g) in
                                          (match uu___14 with
                                           | (f, guard_f) ->
                                               let uu___15 =
                                                 let uu___16 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env bs in
                                                 let uu___17 =
                                                   FStar_Compiler_Effect.op_Bar_Greater
                                                     a.FStar_Syntax_Syntax.binder_bv
                                                     FStar_Syntax_Syntax.bv_to_name in
                                                 fresh_repr r uu___16 u
                                                   uu___17 in
                                               (match uu___15 with
                                                | (ret_t, guard_ret_t) ->
                                                    let uu___16 =
                                                      let uu___17 =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env bs in
                                                      let uu___18 =
                                                        let uu___19 =
                                                          FStar_Ident.string_of_lid
                                                            ed.FStar_Syntax_Syntax.mname in
                                                        FStar_Compiler_Util.format1
                                                          "implicit for pure_wp in checking stronger for %s"
                                                          uu___19 in
                                                      pure_wp_uvar uu___17
                                                        ret_t uu___18 r in
                                                    (match uu___16 with
                                                     | (pure_wp_uvar1,
                                                        guard_wp) ->
                                                         let c =
                                                           let uu___17 =
                                                             let uu___18 =
                                                               let uu___19 =
                                                                 FStar_TypeChecker_Env.new_u_univ
                                                                   () in
                                                               [uu___19] in
                                                             let uu___19 =
                                                               let uu___20 =
                                                                 FStar_Compiler_Effect.op_Bar_Greater
                                                                   pure_wp_uvar1
                                                                   FStar_Syntax_Syntax.as_arg in
                                                               [uu___20] in
                                                             {
                                                               FStar_Syntax_Syntax.comp_univs
                                                                 = uu___18;
                                                               FStar_Syntax_Syntax.effect_name
                                                                 =
                                                                 FStar_Parser_Const.effect_PURE_lid;
                                                               FStar_Syntax_Syntax.result_typ
                                                                 = ret_t;
                                                               FStar_Syntax_Syntax.effect_args
                                                                 = uu___19;
                                                               FStar_Syntax_Syntax.flags
                                                                 = []
                                                             } in
                                                           FStar_Syntax_Syntax.mk_Comp
                                                             uu___17 in
                                                         let k =
                                                           FStar_Syntax_Util.arrow
                                                             (FStar_Compiler_List.op_At
                                                                bs [f]) c in
                                                         ((let uu___18 =
                                                             FStar_Compiler_Effect.op_Less_Bar
                                                               (FStar_TypeChecker_Env.debug
                                                                  env)
                                                               (FStar_Options.Other
                                                                  "LayeredEffectsTc") in
                                                           if uu___18
                                                           then
                                                             let uu___19 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 k in
                                                             FStar_Compiler_Util.print1
                                                               "Expected type of subcomp before unification: %s\n"
                                                               uu___19
                                                           else ());
                                                          (let guard_eq =
                                                             FStar_TypeChecker_Rel.teq
                                                               env ty k in
                                                           FStar_Compiler_List.iter
                                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                                env)
                                                             [guard_f;
                                                             guard_ret_t;
                                                             guard_wp;
                                                             guard_eq];
                                                           (let k1 =
                                                              FStar_Compiler_Effect.op_Bar_Greater
                                                                k
                                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                   env) in
                                                            (let uu___19 =
                                                               let uu___20 =
                                                                 FStar_Syntax_Subst.compress
                                                                   k1 in
                                                               uu___20.FStar_Syntax_Syntax.n in
                                                             match uu___19
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs1, c1) ->
                                                                 let uu___20
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs1 c1 in
                                                                 (match uu___20
                                                                  with
                                                                  | (a1::bs2,
                                                                    c2) ->
                                                                    let res_t
                                                                    =
                                                                    FStar_Syntax_Util.comp_result
                                                                    c2 in
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStar_Compiler_List.splitAt
                                                                    ((FStar_Compiler_List.length
                                                                    bs2) -
                                                                    Prims.int_one)
                                                                    bs2 in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___22
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    match uu___23
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStar_Compiler_List.hd
                                                                    l2 in
                                                                    (l1,
                                                                    uu___24)) in
                                                                    (match uu___21
                                                                    with
                                                                    | 
                                                                    (bs3,
                                                                    f_b) ->
                                                                    let env1
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env 
                                                                    [a1] in
                                                                    validate_layered_effect_binders
                                                                    env1 bs3
                                                                    check_non_informative_binders
                                                                    r)));
                                                            (let uu___19 =
                                                               FStar_Compiler_Effect.op_Bar_Greater
                                                                 k1
                                                                 (FStar_Syntax_Subst.close_univ_vars
                                                                    stronger_us) in
                                                             (stronger_us,
                                                               stronger_t,
                                                               uu___19))))))))))) in
                         log_combinator "stronger_repr" stronger_repr;
                         (let if_then_else =
                            let if_then_else_ts =
                              let ts =
                                let uu___10 =
                                  FStar_Compiler_Effect.op_Bar_Greater ed
                                    FStar_Syntax_Util.get_layered_if_then_else_combinator in
                                FStar_Compiler_Effect.op_Bar_Greater uu___10
                                  FStar_Compiler_Util.must in
                              let uu___10 =
                                let uu___11 =
                                  let uu___12 =
                                    FStar_Compiler_Effect.op_Bar_Greater ts
                                      FStar_Pervasives_Native.snd in
                                  FStar_Compiler_Effect.op_Bar_Greater
                                    uu___12 FStar_Syntax_Subst.compress in
                                uu___11.FStar_Syntax_Syntax.n in
                              match uu___10 with
                              | FStar_Syntax_Syntax.Tm_unknown ->
                                  let signature_ts =
                                    let uu___11 = signature in
                                    match uu___11 with
                                    | (us, t, uu___12) -> (us, t) in
                                  let uu___11 =
                                    FStar_TypeChecker_Env.inst_tscheme_with
                                      signature_ts
                                      [FStar_Syntax_Syntax.U_unknown] in
                                  (match uu___11 with
                                   | (uu___12, signature_t) ->
                                       let uu___13 =
                                         let uu___14 =
                                           FStar_Syntax_Subst.compress
                                             signature_t in
                                         uu___14.FStar_Syntax_Syntax.n in
                                       (match uu___13 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs, uu___14) ->
                                            let bs1 =
                                              FStar_Syntax_Subst.open_binders
                                                bs in
                                            let repr_t =
                                              let repr_ts =
                                                let uu___15 = repr in
                                                match uu___15 with
                                                | (us, t, uu___16) -> (us, t) in
                                              let uu___15 =
                                                FStar_TypeChecker_Env.inst_tscheme_with
                                                  repr_ts
                                                  [FStar_Syntax_Syntax.U_unknown] in
                                              FStar_Compiler_Effect.op_Bar_Greater
                                                uu___15
                                                FStar_Pervasives_Native.snd in
                                            let repr_t_applied =
                                              let uu___15 =
                                                let uu___16 =
                                                  let uu___17 =
                                                    let uu___18 =
                                                      let uu___19 =
                                                        FStar_Compiler_Effect.op_Bar_Greater
                                                          bs1
                                                          (FStar_Compiler_List.map
                                                             (fun b ->
                                                                b.FStar_Syntax_Syntax.binder_bv)) in
                                                      FStar_Compiler_Effect.op_Bar_Greater
                                                        uu___19
                                                        (FStar_Compiler_List.map
                                                           FStar_Syntax_Syntax.bv_to_name) in
                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                      uu___18
                                                      (FStar_Compiler_List.map
                                                         FStar_Syntax_Syntax.as_arg) in
                                                  (repr_t, uu___17) in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu___16 in
                                              FStar_Syntax_Syntax.mk uu___15
                                                FStar_Compiler_Range.dummyRange in
                                            let f_b =
                                              FStar_Syntax_Syntax.null_binder
                                                repr_t_applied in
                                            let g_b =
                                              FStar_Syntax_Syntax.null_binder
                                                repr_t_applied in
                                            let b_b =
                                              FStar_Syntax_Syntax.null_binder
                                                FStar_Syntax_Util.t_bool in
                                            let uu___15 =
                                              FStar_Syntax_Util.abs
                                                (FStar_Compiler_List.op_At
                                                   bs1 [f_b; g_b; b_b])
                                                repr_t_applied
                                                FStar_Pervasives_Native.None in
                                            ([], uu___15)
                                        | uu___14 -> failwith "Impossible!"))
                              | uu___11 -> ts in
                            let r =
                              (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos in
                            let uu___10 =
                              check_and_gen1 "if_then_else" Prims.int_one
                                if_then_else_ts in
                            match uu___10 with
                            | (if_then_else_us, if_then_else_t,
                               if_then_else_ty) ->
                                let uu___11 =
                                  FStar_Syntax_Subst.open_univ_vars
                                    if_then_else_us if_then_else_t in
                                (match uu___11 with
                                 | (us, t) ->
                                     let uu___12 =
                                       FStar_Syntax_Subst.open_univ_vars
                                         if_then_else_us if_then_else_ty in
                                     (match uu___12 with
                                      | (uu___13, ty) ->
                                          let env =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us in
                                          let uu___15 = fresh_a_and_u_a "a" in
                                          (match uu___15 with
                                           | (a, u_a) ->
                                               let rest_bs =
                                                 let uu___16 =
                                                   let uu___17 =
                                                     FStar_Syntax_Subst.compress
                                                       ty in
                                                   uu___17.FStar_Syntax_Syntax.n in
                                                 match uu___16 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs, uu___17) when
                                                     (FStar_Compiler_List.length
                                                        bs)
                                                       >= (Prims.of_int (4))
                                                     ->
                                                     let uu___18 =
                                                       FStar_Syntax_Subst.open_binders
                                                         bs in
                                                     (match uu___18 with
                                                      | {
                                                          FStar_Syntax_Syntax.binder_bv
                                                            = a';
                                                          FStar_Syntax_Syntax.binder_qual
                                                            = uu___19;
                                                          FStar_Syntax_Syntax.binder_attrs
                                                            = uu___20;_}::bs1
                                                          ->
                                                          let uu___21 =
                                                            let uu___22 =
                                                              FStar_Compiler_Effect.op_Bar_Greater
                                                                bs1
                                                                (FStar_Compiler_List.splitAt
                                                                   ((FStar_Compiler_List.length
                                                                    bs1) -
                                                                    (Prims.of_int (3)))) in
                                                            FStar_Compiler_Effect.op_Bar_Greater
                                                              uu___22
                                                              FStar_Pervasives_Native.fst in
                                                          let uu___22 =
                                                            let uu___23 =
                                                              let uu___24 =
                                                                let uu___25 =
                                                                  let uu___26
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    a.FStar_Syntax_Syntax.binder_bv
                                                                    FStar_Syntax_Syntax.bv_to_name in
                                                                  (a',
                                                                    uu___26) in
                                                                FStar_Syntax_Syntax.NT
                                                                  uu___25 in
                                                              [uu___24] in
                                                            FStar_Syntax_Subst.subst_binders
                                                              uu___23 in
                                                          FStar_Compiler_Effect.op_Bar_Greater
                                                            uu___21 uu___22)
                                                 | uu___17 ->
                                                     not_an_arrow_error
                                                       "if_then_else"
                                                       (Prims.of_int (4)) ty
                                                       r in
                                               let bs = a :: rest_bs in
                                               let uu___16 =
                                                 let uu___17 =
                                                   let uu___18 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs in
                                                   let uu___19 =
                                                     FStar_Compiler_Effect.op_Bar_Greater
                                                       a.FStar_Syntax_Syntax.binder_bv
                                                       FStar_Syntax_Syntax.bv_to_name in
                                                   fresh_repr r uu___18 u_a
                                                     uu___19 in
                                                 match uu___17 with
                                                 | (repr1, g) ->
                                                     let uu___18 =
                                                       let uu___19 =
                                                         FStar_Syntax_Syntax.gen_bv
                                                           "f"
                                                           FStar_Pervasives_Native.None
                                                           repr1 in
                                                       FStar_Compiler_Effect.op_Bar_Greater
                                                         uu___19
                                                         FStar_Syntax_Syntax.mk_binder in
                                                     (uu___18, g) in
                                               (match uu___16 with
                                                | (f_bs, guard_f) ->
                                                    let uu___17 =
                                                      let uu___18 =
                                                        let uu___19 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env bs in
                                                        let uu___20 =
                                                          FStar_Compiler_Effect.op_Bar_Greater
                                                            a.FStar_Syntax_Syntax.binder_bv
                                                            FStar_Syntax_Syntax.bv_to_name in
                                                        fresh_repr r uu___19
                                                          u_a uu___20 in
                                                      match uu___18 with
                                                      | (repr1, g) ->
                                                          let uu___19 =
                                                            let uu___20 =
                                                              FStar_Syntax_Syntax.gen_bv
                                                                "g"
                                                                FStar_Pervasives_Native.None
                                                                repr1 in
                                                            FStar_Compiler_Effect.op_Bar_Greater
                                                              uu___20
                                                              FStar_Syntax_Syntax.mk_binder in
                                                          (uu___19, g) in
                                                    (match uu___17 with
                                                     | (g_bs, guard_g) ->
                                                         let p_b =
                                                           let uu___18 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "p"
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Util.t_bool in
                                                           FStar_Compiler_Effect.op_Bar_Greater
                                                             uu___18
                                                             FStar_Syntax_Syntax.mk_binder in
                                                         let uu___18 =
                                                           let uu___19 =
                                                             FStar_TypeChecker_Env.push_binders
                                                               env
                                                               (FStar_Compiler_List.op_At
                                                                  bs 
                                                                  [p_b]) in
                                                           let uu___20 =
                                                             FStar_Compiler_Effect.op_Bar_Greater
                                                               a.FStar_Syntax_Syntax.binder_bv
                                                               FStar_Syntax_Syntax.bv_to_name in
                                                           fresh_repr r
                                                             uu___19 u_a
                                                             uu___20 in
                                                         (match uu___18 with
                                                          | (t_body,
                                                             guard_body) ->
                                                              let k =
                                                                FStar_Syntax_Util.abs
                                                                  (FStar_Compiler_List.op_At
                                                                    bs
                                                                    [f_bs;
                                                                    g_bs;
                                                                    p_b])
                                                                  t_body
                                                                  FStar_Pervasives_Native.None in
                                                              let guard_eq =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env t k in
                                                              (FStar_Compiler_Effect.op_Bar_Greater
                                                                 [guard_f;
                                                                 guard_g;
                                                                 guard_body;
                                                                 guard_eq]
                                                                 (FStar_Compiler_List.iter
                                                                    (
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env));
                                                               (let k1 =
                                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                                    k
                                                                    (
                                                                    FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                    env) in
                                                                (let uu___20
                                                                   =
                                                                   let uu___21
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    k1 in
                                                                   uu___21.FStar_Syntax_Syntax.n in
                                                                 match uu___20
                                                                 with
                                                                 | FStar_Syntax_Syntax.Tm_abs
                                                                    (bs1,
                                                                    body,
                                                                    uu___21)
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStar_Syntax_Subst.open_term
                                                                    bs1 body in
                                                                    (match uu___22
                                                                    with
                                                                    | 
                                                                    (a1::bs2,
                                                                    body1) ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStar_Compiler_List.splitAt
                                                                    ((FStar_Compiler_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (3)))
                                                                    bs2 in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___24
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    match uu___25
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    l2
                                                                    FStar_Compiler_List.hd in
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    l2
                                                                    FStar_Compiler_List.tl in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___28
                                                                    FStar_Compiler_List.hd in
                                                                    (l1,
                                                                    uu___26,
                                                                    uu___27)) in
                                                                    (match uu___23
                                                                    with
                                                                    | 
                                                                    (bs3,
                                                                    f_b, g_b)
                                                                    ->
                                                                    let env1
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env 
                                                                    [a1] in
                                                                    validate_layered_effect_binders
                                                                    env1 bs3
                                                                    check_non_informative_binders
                                                                    r)));
                                                                (let uu___20
                                                                   =
                                                                   FStar_Compiler_Effect.op_Bar_Greater
                                                                    k1
                                                                    (FStar_Syntax_Subst.close_univ_vars
                                                                    if_then_else_us) in
                                                                 (if_then_else_us,
                                                                   uu___20,
                                                                   if_then_else_ty)))))))))) in
                          log_combinator "if_then_else" if_then_else;
                          FStar_Errors.with_ctx
                            "While checking if-then-else soundness"
                            (fun uu___11 ->
                               let r =
                                 let uu___12 =
                                   let uu___13 =
                                     let uu___14 =
                                       FStar_Compiler_Effect.op_Bar_Greater
                                         ed
                                         FStar_Syntax_Util.get_layered_if_then_else_combinator in
                                     FStar_Compiler_Effect.op_Bar_Greater
                                       uu___14 FStar_Compiler_Util.must in
                                   FStar_Compiler_Effect.op_Bar_Greater
                                     uu___13 FStar_Pervasives_Native.snd in
                                 uu___12.FStar_Syntax_Syntax.pos in
                               let uu___12 = if_then_else in
                               match uu___12 with
                               | (ite_us, ite_t, uu___13) ->
                                   let uu___14 =
                                     FStar_Syntax_Subst.open_univ_vars ite_us
                                       ite_t in
                                   (match uu___14 with
                                    | (us, ite_t1) ->
                                        let uu___15 =
                                          let uu___16 =
                                            let uu___17 =
                                              FStar_Syntax_Subst.compress
                                                ite_t1 in
                                            uu___17.FStar_Syntax_Syntax.n in
                                          match uu___16 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (bs, uu___17, uu___18) ->
                                              let bs1 =
                                                FStar_Syntax_Subst.open_binders
                                                  bs in
                                              let uu___19 =
                                                let uu___20 =
                                                  let uu___21 =
                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                      bs1
                                                      (FStar_Compiler_List.splitAt
                                                         ((FStar_Compiler_List.length
                                                             bs1)
                                                            -
                                                            (Prims.of_int (3)))) in
                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                    uu___21
                                                    FStar_Pervasives_Native.snd in
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  uu___20
                                                  (fun l ->
                                                     let uu___21 = l in
                                                     match uu___21 with
                                                     | f::g::p::[] ->
                                                         (f, g, p)) in
                                              (match uu___19 with
                                               | (f_b, g_b, p_b) ->
                                                   let env =
                                                     let uu___20 =
                                                       FStar_TypeChecker_Env.push_univ_vars
                                                         env0 us in
                                                     FStar_TypeChecker_Env.push_binders
                                                       uu___20 bs1 in
                                                   let uu___20 =
                                                     let uu___21 =
                                                       let uu___22 =
                                                         FStar_Compiler_Effect.op_Bar_Greater
                                                           bs1
                                                           (FStar_Compiler_List.map
                                                              (fun b ->
                                                                 let uu___23
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    b.FStar_Syntax_Syntax.binder_bv in
                                                                 let uu___24
                                                                   =
                                                                   FStar_Syntax_Util.aqual_of_binder
                                                                    b in
                                                                 (uu___23,
                                                                   uu___24))) in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         ite_t1 uu___22 r in
                                                     FStar_Compiler_Effect.op_Bar_Greater
                                                       uu___21
                                                       (FStar_TypeChecker_Normalize.normalize
                                                          [FStar_TypeChecker_Env.Beta]
                                                          env) in
                                                   let uu___21 =
                                                     FStar_Compiler_Effect.op_Bar_Greater
                                                       bs1
                                                       FStar_Compiler_List.hd in
                                                   let uu___22 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       p_b.FStar_Syntax_Syntax.binder_bv in
                                                   (env, uu___20, uu___21,
                                                     f_b, g_b, uu___22))
                                          | uu___17 ->
                                              failwith
                                                "Impossible! ite_t must have been an abstraction with at least 3 binders" in
                                        (match uu___15 with
                                         | (env, ite_t_applied, a_b, f_b,
                                            g_b, p_t) ->
                                             let uu___16 =
                                               let uu___17 = stronger_repr in
                                               match uu___17 with
                                               | (uu___18, uu___19,
                                                  subcomp_ty) ->
                                                   let uu___20 =
                                                     FStar_Syntax_Subst.open_univ_vars
                                                       us subcomp_ty in
                                                   (match uu___20 with
                                                    | (uu___21, subcomp_ty1)
                                                        ->
                                                        let uu___22 =
                                                          let uu___23 =
                                                            FStar_Syntax_Subst.compress
                                                              subcomp_ty1 in
                                                          uu___23.FStar_Syntax_Syntax.n in
                                                        (match uu___22 with
                                                         | FStar_Syntax_Syntax.Tm_arrow
                                                             (bs, c) ->
                                                             let uu___23 =
                                                               FStar_Syntax_Subst.open_comp
                                                                 bs c in
                                                             (match uu___23
                                                              with
                                                              | (bs1, c1) ->
                                                                  let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStar_Compiler_List.hd
                                                                    bs1 in
                                                                    let uu___26
                                                                    =
                                                                    FStar_Compiler_List.tl
                                                                    bs1 in
                                                                    (uu___25,
                                                                    uu___26) in
                                                                  (match uu___24
                                                                   with
                                                                   | 
                                                                   (a_b1,
                                                                    rest_bs)
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    rest_bs
                                                                    (FStar_Compiler_List.splitAt
                                                                    ((FStar_Compiler_List.length
                                                                    rest_bs)
                                                                    -
                                                                    Prims.int_one)) in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___26
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    match uu___27
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStar_Compiler_List.hd
                                                                    l2 in
                                                                    (l1,
                                                                    uu___28)) in
                                                                    (match uu___25
                                                                    with
                                                                    | 
                                                                    (rest_bs1,
                                                                    f_b1) ->
                                                                    (a_b1,
                                                                    rest_bs1,
                                                                    f_b1, c1))))
                                                         | uu___23 ->
                                                             failwith
                                                               "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")) in
                                             (match uu___16 with
                                              | (subcomp_a_b, subcomp_bs,
                                                 subcomp_f_b, subcomp_c) ->
                                                  let check_branch env1
                                                    ite_f_or_g_sort attr_opt
                                                    =
                                                    let uu___17 =
                                                      let uu___18 =
                                                        let uu___19 =
                                                          let uu___20 =
                                                            let uu___21 =
                                                              let uu___22 =
                                                                let uu___23 =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a_b.FStar_Syntax_Syntax.binder_bv in
                                                                ((subcomp_a_b.FStar_Syntax_Syntax.binder_bv),
                                                                  uu___23) in
                                                              FStar_Syntax_Syntax.NT
                                                                uu___22 in
                                                            [uu___21] in
                                                          (uu___20, [],
                                                            FStar_TypeChecker_Env.trivial_guard) in
                                                        FStar_Compiler_List.fold_left
                                                          (fun uu___20 ->
                                                             fun b ->
                                                               match uu___20
                                                               with
                                                               | (subst,
                                                                  uvars, g)
                                                                   ->
                                                                   let sort =
                                                                    FStar_Syntax_Subst.subst
                                                                    subst
                                                                    (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                                                   let uu___21
                                                                    =
                                                                    let uv_qual
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    ((FStar_Compiler_List.length
                                                                    b.FStar_Syntax_Syntax.binder_attrs)
                                                                    >
                                                                    Prims.int_zero)
                                                                    ||
                                                                    (FStar_Compiler_Effect.op_Bar_Greater
                                                                    attr_opt
                                                                    FStar_Compiler_Util.is_some) in
                                                                    if
                                                                    uu___22
                                                                    then
                                                                    FStar_Syntax_Syntax.Strict
                                                                    else
                                                                    FStar_Syntax_Syntax.Allow_untyped
                                                                    "effect ite binder" in
                                                                    let ctx_uvar_meta
                                                                    =
                                                                    FStar_Compiler_Util.map_option
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                                                    uu___22)
                                                                    attr_opt in
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_Syntax_Print.binder_to_string
                                                                    b in
                                                                    FStar_Compiler_Util.format1
                                                                    "uvar for subcomp %s binder when checking ite soundness"
                                                                    uu___23 in
                                                                    FStar_TypeChecker_Env.new_implicit_var
                                                                    uu___22 r
                                                                    env1 sort
                                                                    uv_qual
                                                                    ctx_uvar_meta in
                                                                   (match uu___21
                                                                    with
                                                                    | 
                                                                    (t,
                                                                    uu___22,
                                                                    g_t) ->
                                                                    let uu___23
                                                                    =
                                                                    FStar_TypeChecker_Common.conj_guard
                                                                    g g_t in
                                                                    ((FStar_Compiler_List.op_At
                                                                    subst
                                                                    [
                                                                    FStar_Syntax_Syntax.NT
                                                                    ((b.FStar_Syntax_Syntax.binder_bv),
                                                                    t)]),
                                                                    (FStar_Compiler_List.op_At
                                                                    uvars 
                                                                    [t]),
                                                                    uu___23)))
                                                          uu___19 in
                                                      FStar_Compiler_Effect.op_Bar_Greater
                                                        subcomp_bs uu___18 in
                                                    match uu___17 with
                                                    | (subst, uvars, g_uvars)
                                                        ->
                                                        let subcomp_f_sort =
                                                          FStar_Syntax_Subst.subst
                                                            subst
                                                            (subcomp_f_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                                        let c =
                                                          let uu___18 =
                                                            FStar_Syntax_Subst.subst_comp
                                                              subst subcomp_c in
                                                          FStar_Compiler_Effect.op_Bar_Greater
                                                            uu___18
                                                            (FStar_TypeChecker_Env.unfold_effect_abbrev
                                                               env1) in
                                                        let g_f_or_g =
                                                          FStar_TypeChecker_Rel.layered_effect_teq
                                                            env1
                                                            subcomp_f_sort
                                                            ite_f_or_g_sort
                                                            FStar_Pervasives_Native.None in
                                                        let g_c =
                                                          FStar_TypeChecker_Rel.layered_effect_teq
                                                            env1
                                                            c.FStar_Syntax_Syntax.result_typ
                                                            ite_t_applied
                                                            FStar_Pervasives_Native.None in
                                                        let fml =
                                                          let uu___18 =
                                                            FStar_Compiler_List.hd
                                                              c.FStar_Syntax_Syntax.comp_univs in
                                                          let uu___19 =
                                                            let uu___20 =
                                                              FStar_Compiler_Effect.op_Bar_Greater
                                                                c.FStar_Syntax_Syntax.effect_args
                                                                FStar_Compiler_List.hd in
                                                            FStar_Compiler_Effect.op_Bar_Greater
                                                              uu___20
                                                              FStar_Pervasives_Native.fst in
                                                          FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                            env1 uu___18
                                                            c.FStar_Syntax_Syntax.result_typ
                                                            uu___19 r in
                                                        let g_precondition =
                                                          match attr_opt with
                                                          | FStar_Pervasives_Native.None
                                                              ->
                                                              let uu___18 =
                                                                FStar_Compiler_Effect.op_Bar_Greater
                                                                  fml
                                                                  (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_TypeChecker_Common.NonTrivial
                                                                    uu___19) in
                                                              FStar_Compiler_Effect.op_Bar_Greater
                                                                uu___18
                                                                FStar_TypeChecker_Env.guard_of_guard_formula
                                                          | FStar_Pervasives_Native.Some
                                                              attr ->
                                                              let uu___18 =
                                                                let uu___19 =
                                                                  FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    fml in
                                                                let uu___20 =
                                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                                    (
                                                                    FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                                                    attr)
                                                                    (
                                                                    fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___21) in
                                                                FStar_TypeChecker_Env.new_implicit_var
                                                                  "" r env1
                                                                  uu___19
                                                                  FStar_Syntax_Syntax.Strict
                                                                  uu___20 in
                                                              (match uu___18
                                                               with
                                                               | (uu___19,
                                                                  uu___20, g)
                                                                   -> g) in
                                                        let uu___18 =
                                                          FStar_TypeChecker_Env.conj_guards
                                                            [g_uvars;
                                                            g_f_or_g;
                                                            g_c;
                                                            g_precondition] in
                                                        FStar_TypeChecker_Rel.force_trivial_guard
                                                          env1 uu___18 in
                                                  let ite_soundness_tac_attr
                                                    =
                                                    let uu___17 =
                                                      FStar_Syntax_Util.get_attribute
                                                        FStar_Parser_Const.ite_soundness_by_attr
                                                        attrs in
                                                    match uu___17 with
                                                    | FStar_Pervasives_Native.Some
                                                        ((t, uu___18)::uu___19)
                                                        ->
                                                        FStar_Pervasives_Native.Some
                                                          t
                                                    | uu___18 ->
                                                        FStar_Pervasives_Native.None in
                                                  ((let env1 =
                                                      let uu___17 =
                                                        let uu___18 =
                                                          let uu___19 =
                                                            FStar_Compiler_Effect.op_Bar_Greater
                                                              p_t
                                                              FStar_Syntax_Util.b2t in
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            uu___19 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          FStar_Pervasives_Native.None
                                                          uu___18 in
                                                      FStar_TypeChecker_Env.push_bv
                                                        env uu___17 in
                                                    check_branch env1
                                                      (f_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                                      ite_soundness_tac_attr);
                                                   (let not_p =
                                                      let uu___17 =
                                                        let uu___18 =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            FStar_Parser_Const.not_lid
                                                            FStar_Syntax_Syntax.delta_constant
                                                            FStar_Pervasives_Native.None in
                                                        FStar_Compiler_Effect.op_Bar_Greater
                                                          uu___18
                                                          FStar_Syntax_Syntax.fv_to_tm in
                                                      let uu___18 =
                                                        let uu___19 =
                                                          let uu___20 =
                                                            FStar_Compiler_Effect.op_Bar_Greater
                                                              p_t
                                                              FStar_Syntax_Util.b2t in
                                                          FStar_Compiler_Effect.op_Bar_Greater
                                                            uu___20
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu___19] in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu___17 uu___18 r in
                                                    let env1 =
                                                      let uu___17 =
                                                        FStar_Syntax_Syntax.new_bv
                                                          FStar_Pervasives_Native.None
                                                          not_p in
                                                      FStar_TypeChecker_Env.push_bv
                                                        env uu___17 in
                                                    check_branch env1
                                                      (g_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                                      ite_soundness_tac_attr))))));
                          (let tc_action env act =
                             let env01 = env in
                             let r =
                               (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                             if
                               (FStar_Compiler_List.length
                                  act.FStar_Syntax_Syntax.action_params)
                                 <> Prims.int_zero
                             then
                               (let uu___12 =
                                  let uu___13 =
                                    let uu___14 =
                                      FStar_Ident.string_of_lid
                                        ed.FStar_Syntax_Syntax.mname in
                                    let uu___15 =
                                      FStar_Ident.string_of_lid
                                        act.FStar_Syntax_Syntax.action_name in
                                    let uu___16 =
                                      FStar_Syntax_Print.binders_to_string
                                        "; "
                                        act.FStar_Syntax_Syntax.action_params in
                                    FStar_Compiler_Util.format3
                                      "Action %s:%s has non-empty action params (%s)"
                                      uu___14 uu___15 uu___16 in
                                  (FStar_Errors.Fatal_MalformedActionDeclaration,
                                    uu___13) in
                                FStar_Errors.raise_error uu___12 r)
                             else ();
                             (let uu___12 =
                                let uu___13 =
                                  FStar_Syntax_Subst.univ_var_opening
                                    act.FStar_Syntax_Syntax.action_univs in
                                match uu___13 with
                                | (usubst, us) ->
                                    let uu___14 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env us in
                                    let uu___15 =
                                      let uu___16 =
                                        FStar_Syntax_Subst.subst usubst
                                          act.FStar_Syntax_Syntax.action_defn in
                                      let uu___17 =
                                        FStar_Syntax_Subst.subst usubst
                                          act.FStar_Syntax_Syntax.action_typ in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (act.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (act.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs = us;
                                        FStar_Syntax_Syntax.action_params =
                                          (act.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu___16;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu___17
                                      } in
                                    (uu___14, uu___15) in
                              match uu___12 with
                              | (env1, act1) ->
                                  let act_typ =
                                    let uu___13 =
                                      let uu___14 =
                                        FStar_Syntax_Subst.compress
                                          act1.FStar_Syntax_Syntax.action_typ in
                                      uu___14.FStar_Syntax_Syntax.n in
                                    match uu___13 with
                                    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                                        let ct =
                                          FStar_Syntax_Util.comp_to_comp_typ
                                            c in
                                        let uu___14 =
                                          FStar_Ident.lid_equals
                                            ct.FStar_Syntax_Syntax.effect_name
                                            ed.FStar_Syntax_Syntax.mname in
                                        if uu___14
                                        then
                                          let repr_ts =
                                            let uu___15 = repr in
                                            match uu___15 with
                                            | (us, t, uu___16) -> (us, t) in
                                          let repr1 =
                                            let uu___15 =
                                              FStar_TypeChecker_Env.inst_tscheme_with
                                                repr_ts
                                                ct.FStar_Syntax_Syntax.comp_univs in
                                            FStar_Compiler_Effect.op_Bar_Greater
                                              uu___15
                                              FStar_Pervasives_Native.snd in
                                          let repr2 =
                                            let uu___15 =
                                              let uu___16 =
                                                FStar_Syntax_Syntax.as_arg
                                                  ct.FStar_Syntax_Syntax.result_typ in
                                              uu___16 ::
                                                (ct.FStar_Syntax_Syntax.effect_args) in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              repr1 uu___15 r in
                                          let c1 =
                                            let uu___15 =
                                              let uu___16 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              FStar_Pervasives_Native.Some
                                                uu___16 in
                                            FStar_Syntax_Syntax.mk_Total'
                                              repr2 uu___15 in
                                          FStar_Syntax_Util.arrow bs c1
                                        else
                                          act1.FStar_Syntax_Syntax.action_typ
                                    | uu___14 ->
                                        act1.FStar_Syntax_Syntax.action_typ in
                                  let uu___13 =
                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                      env1 act_typ in
                                  (match uu___13 with
                                   | (act_typ1, uu___14, g_t) ->
                                       let uu___15 =
                                         let uu___16 =
                                           let uu___17 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ1 in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___17.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___17.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___17.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___17.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_sig
                                               =
                                               (uu___17.FStar_TypeChecker_Env.gamma_sig);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___17.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___17.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___17.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___17.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.attrtab =
                                               (uu___17.FStar_TypeChecker_Env.attrtab);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___17.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___17.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___17.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___17.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___17.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq_strict
                                               =
                                               (uu___17.FStar_TypeChecker_Env.use_eq_strict);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___17.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___17.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___17.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___17.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.phase1 =
                                               (uu___17.FStar_TypeChecker_Env.phase1);
                                             FStar_TypeChecker_Env.failhard =
                                               (uu___17.FStar_TypeChecker_Env.failhard);
                                             FStar_TypeChecker_Env.nosynth =
                                               (uu___17.FStar_TypeChecker_Env.nosynth);
                                             FStar_TypeChecker_Env.uvar_subtyping
                                               =
                                               (uu___17.FStar_TypeChecker_Env.uvar_subtyping);
                                             FStar_TypeChecker_Env.tc_term =
                                               (uu___17.FStar_TypeChecker_Env.tc_term);
                                             FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                               =
                                               (uu___17.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___17.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                               =
                                               (uu___17.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                             FStar_TypeChecker_Env.teq_nosmt_force
                                               =
                                               (uu___17.FStar_TypeChecker_Env.teq_nosmt_force);
                                             FStar_TypeChecker_Env.subtype_nosmt_force
                                               =
                                               (uu___17.FStar_TypeChecker_Env.subtype_nosmt_force);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___17.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qtbl_name_and_index
                                               =
                                               (uu___17.FStar_TypeChecker_Env.qtbl_name_and_index);
                                             FStar_TypeChecker_Env.normalized_eff_names
                                               =
                                               (uu___17.FStar_TypeChecker_Env.normalized_eff_names);
                                             FStar_TypeChecker_Env.fv_delta_depths
                                               =
                                               (uu___17.FStar_TypeChecker_Env.fv_delta_depths);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___17.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth_hook
                                               =
                                               (uu___17.FStar_TypeChecker_Env.synth_hook);
                                             FStar_TypeChecker_Env.try_solve_implicits_hook
                                               =
                                               (uu___17.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                             FStar_TypeChecker_Env.splice =
                                               (uu___17.FStar_TypeChecker_Env.splice);
                                             FStar_TypeChecker_Env.mpreprocess
                                               =
                                               (uu___17.FStar_TypeChecker_Env.mpreprocess);
                                             FStar_TypeChecker_Env.postprocess
                                               =
                                               (uu___17.FStar_TypeChecker_Env.postprocess);
                                             FStar_TypeChecker_Env.identifier_info
                                               =
                                               (uu___17.FStar_TypeChecker_Env.identifier_info);
                                             FStar_TypeChecker_Env.tc_hooks =
                                               (uu___17.FStar_TypeChecker_Env.tc_hooks);
                                             FStar_TypeChecker_Env.dsenv =
                                               (uu___17.FStar_TypeChecker_Env.dsenv);
                                             FStar_TypeChecker_Env.nbe =
                                               (uu___17.FStar_TypeChecker_Env.nbe);
                                             FStar_TypeChecker_Env.strict_args_tab
                                               =
                                               (uu___17.FStar_TypeChecker_Env.strict_args_tab);
                                             FStar_TypeChecker_Env.erasable_types_tab
                                               =
                                               (uu___17.FStar_TypeChecker_Env.erasable_types_tab);
                                             FStar_TypeChecker_Env.enable_defer_to_tac
                                               =
                                               (uu___17.FStar_TypeChecker_Env.enable_defer_to_tac);
                                             FStar_TypeChecker_Env.unif_allow_ref_guards
                                               =
                                               (uu___17.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                             FStar_TypeChecker_Env.erase_erasable_args
                                               =
                                               (uu___17.FStar_TypeChecker_Env.erase_erasable_args);
                                             FStar_TypeChecker_Env.core_check
                                               =
                                               (uu___17.FStar_TypeChecker_Env.core_check)
                                           } in
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           uu___16
                                           act1.FStar_Syntax_Syntax.action_defn in
                                       (match uu___15 with
                                        | (act_defn, uu___16, g_d) ->
                                            ((let uu___18 =
                                                FStar_Compiler_Effect.op_Less_Bar
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffectsTc") in
                                              if uu___18
                                              then
                                                let uu___19 =
                                                  FStar_Syntax_Print.term_to_string
                                                    act_defn in
                                                let uu___20 =
                                                  FStar_Syntax_Print.term_to_string
                                                    act_typ1 in
                                                FStar_Compiler_Util.print2
                                                  "Typechecked action definition: %s and action type: %s\n"
                                                  uu___19 uu___20
                                              else ());
                                             (let uu___18 =
                                                let act_typ2 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 act_typ1 in
                                                let uu___19 =
                                                  let uu___20 =
                                                    FStar_Syntax_Subst.compress
                                                      act_typ2 in
                                                  uu___20.FStar_Syntax_Syntax.n in
                                                match uu___19 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs, uu___20) ->
                                                    let bs1 =
                                                      FStar_Syntax_Subst.open_binders
                                                        bs in
                                                    let env2 =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env1 bs1 in
                                                    let uu___21 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    (match uu___21 with
                                                     | (t, u) ->
                                                         let reason =
                                                           let uu___22 =
                                                             FStar_Ident.string_of_lid
                                                               ed.FStar_Syntax_Syntax.mname in
                                                           let uu___23 =
                                                             FStar_Ident.string_of_lid
                                                               act1.FStar_Syntax_Syntax.action_name in
                                                           FStar_Compiler_Util.format2
                                                             "implicit for return type of action %s:%s"
                                                             uu___22 uu___23 in
                                                         let uu___22 =
                                                           FStar_TypeChecker_Util.new_implicit_var
                                                             reason r env2 t in
                                                         (match uu___22 with
                                                          | (a_tm, uu___23,
                                                             g_tm) ->
                                                              let uu___24 =
                                                                fresh_repr r
                                                                  env2 u a_tm in
                                                              (match uu___24
                                                               with
                                                               | (repr1, g)
                                                                   ->
                                                                   let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    () in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___28
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___29) in
                                                                    FStar_Syntax_Syntax.mk_Total'
                                                                    repr1
                                                                    uu___27 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu___26 in
                                                                   let uu___26
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g g_tm in
                                                                   (uu___25,
                                                                    uu___26))))
                                                | uu___20 ->
                                                    let uu___21 =
                                                      let uu___22 =
                                                        let uu___23 =
                                                          FStar_Ident.string_of_lid
                                                            ed.FStar_Syntax_Syntax.mname in
                                                        let uu___24 =
                                                          FStar_Ident.string_of_lid
                                                            act1.FStar_Syntax_Syntax.action_name in
                                                        let uu___25 =
                                                          FStar_Syntax_Print.term_to_string
                                                            act_typ2 in
                                                        FStar_Compiler_Util.format3
                                                          "Unexpected non-function type for action %s:%s (%s)"
                                                          uu___23 uu___24
                                                          uu___25 in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu___22) in
                                                    FStar_Errors.raise_error
                                                      uu___21 r in
                                              match uu___18 with
                                              | (k, g_k) ->
                                                  ((let uu___20 =
                                                      FStar_Compiler_Effect.op_Less_Bar
                                                        (FStar_TypeChecker_Env.debug
                                                           env1)
                                                        (FStar_Options.Other
                                                           "LayeredEffectsTc") in
                                                    if uu___20
                                                    then
                                                      let uu___21 =
                                                        FStar_Syntax_Print.term_to_string
                                                          k in
                                                      FStar_Compiler_Util.print1
                                                        "Expected action type: %s\n"
                                                        uu___21
                                                    else ());
                                                   (let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1 k in
                                                    FStar_Compiler_List.iter
                                                      (FStar_TypeChecker_Rel.force_trivial_guard
                                                         env1)
                                                      [g_t; g_d; g_k; g];
                                                    (let uu___22 =
                                                       FStar_Compiler_Effect.op_Less_Bar
                                                         (FStar_TypeChecker_Env.debug
                                                            env1)
                                                         (FStar_Options.Other
                                                            "LayeredEffectsTc") in
                                                     if uu___22
                                                     then
                                                       let uu___23 =
                                                         FStar_Syntax_Print.term_to_string
                                                           k in
                                                       FStar_Compiler_Util.print1
                                                         "Expected action type after unification: %s\n"
                                                         uu___23
                                                     else ());
                                                    (let act_typ2 =
                                                       let err_msg t =
                                                         let uu___22 =
                                                           FStar_Ident.string_of_lid
                                                             ed.FStar_Syntax_Syntax.mname in
                                                         let uu___23 =
                                                           FStar_Ident.string_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name in
                                                         let uu___24 =
                                                           FStar_Syntax_Print.term_to_string
                                                             t in
                                                         FStar_Compiler_Util.format3
                                                           "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                           uu___22 uu___23
                                                           uu___24 in
                                                       let repr_args t =
                                                         let uu___22 =
                                                           let uu___23 =
                                                             FStar_Syntax_Subst.compress
                                                               t in
                                                           uu___23.FStar_Syntax_Syntax.n in
                                                         match uu___22 with
                                                         | FStar_Syntax_Syntax.Tm_app
                                                             (head, a::is) ->
                                                             let uu___23 =
                                                               let uu___24 =
                                                                 FStar_Syntax_Subst.compress
                                                                   head in
                                                               uu___24.FStar_Syntax_Syntax.n in
                                                             (match uu___23
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_uinst
                                                                  (uu___24,
                                                                   us)
                                                                  ->
                                                                  (us,
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    a), is)
                                                              | uu___24 ->
                                                                  let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    err_msg t in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu___26) in
                                                                  FStar_Errors.raise_error
                                                                    uu___25 r)
                                                         | uu___23 ->
                                                             let uu___24 =
                                                               let uu___25 =
                                                                 err_msg t in
                                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                 uu___25) in
                                                             FStar_Errors.raise_error
                                                               uu___24 r in
                                                       let k1 =
                                                         FStar_TypeChecker_Normalize.normalize
                                                           [FStar_TypeChecker_Env.Beta]
                                                           env1 k in
                                                       let uu___22 =
                                                         let uu___23 =
                                                           FStar_Syntax_Subst.compress
                                                             k1 in
                                                         uu___23.FStar_Syntax_Syntax.n in
                                                       match uu___22 with
                                                       | FStar_Syntax_Syntax.Tm_arrow
                                                           (bs, c) ->
                                                           let uu___23 =
                                                             FStar_Syntax_Subst.open_comp
                                                               bs c in
                                                           (match uu___23
                                                            with
                                                            | (bs1, c1) ->
                                                                let uu___24 =
                                                                  repr_args
                                                                    (
                                                                    FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                (match uu___24
                                                                 with
                                                                 | (us, a,
                                                                    is) ->
                                                                    let ct =
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    = us;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    = is;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu___25
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    ct in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu___25))
                                                       | uu___23 ->
                                                           let uu___24 =
                                                             let uu___25 =
                                                               err_msg k1 in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu___25) in
                                                           FStar_Errors.raise_error
                                                             uu___24 r in
                                                     (let uu___23 =
                                                        FStar_Compiler_Effect.op_Less_Bar
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          (FStar_Options.Other
                                                             "LayeredEffectsTc") in
                                                      if uu___23
                                                      then
                                                        let uu___24 =
                                                          FStar_Syntax_Print.term_to_string
                                                            act_typ2 in
                                                        FStar_Compiler_Util.print1
                                                          "Action type after injecting it into the monad: %s\n"
                                                          uu___24
                                                      else ());
                                                     (let act2 =
                                                        let uu___23 =
                                                          FStar_TypeChecker_Generalize.generalize_universes
                                                            env1 act_defn in
                                                        match uu___23 with
                                                        | (us, act_defn1) ->
                                                            if
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                                = []
                                                            then
                                                              let uu___24 =
                                                                FStar_Syntax_Subst.close_univ_vars
                                                                  us act_typ2 in
                                                              {
                                                                FStar_Syntax_Syntax.action_name
                                                                  =
                                                                  (act1.FStar_Syntax_Syntax.action_name);
                                                                FStar_Syntax_Syntax.action_unqualified_name
                                                                  =
                                                                  (act1.FStar_Syntax_Syntax.action_unqualified_name);
                                                                FStar_Syntax_Syntax.action_univs
                                                                  = us;
                                                                FStar_Syntax_Syntax.action_params
                                                                  =
                                                                  (act1.FStar_Syntax_Syntax.action_params);
                                                                FStar_Syntax_Syntax.action_defn
                                                                  = act_defn1;
                                                                FStar_Syntax_Syntax.action_typ
                                                                  = uu___24
                                                              }
                                                            else
                                                              (let uu___25 =
                                                                 ((FStar_Compiler_List.length
                                                                    us) =
                                                                    (
                                                                    FStar_Compiler_List.length
                                                                    act1.FStar_Syntax_Syntax.action_univs))
                                                                   &&
                                                                   (FStar_Compiler_List.forall2
                                                                    (fun u1
                                                                    ->
                                                                    fun u2 ->
                                                                    let uu___26
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2 in
                                                                    uu___26 =
                                                                    Prims.int_zero)
                                                                    us
                                                                    act1.FStar_Syntax_Syntax.action_univs) in
                                                               if uu___25
                                                               then
                                                                 let uu___26
                                                                   =
                                                                   FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_typ2 in
                                                                 {
                                                                   FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (act1.FStar_Syntax_Syntax.action_name);
                                                                   FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (act1.FStar_Syntax_Syntax.action_unqualified_name);
                                                                   FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (act1.FStar_Syntax_Syntax.action_univs);
                                                                   FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (act1.FStar_Syntax_Syntax.action_params);
                                                                   FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn1;
                                                                   FStar_Syntax_Syntax.action_typ
                                                                    = uu___26
                                                                 }
                                                               else
                                                                 (let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    ed.FStar_Syntax_Syntax.mname in
                                                                    let uu___30
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    act1.FStar_Syntax_Syntax.action_name in
                                                                    let uu___31
                                                                    =
                                                                    FStar_Syntax_Print.univ_names_to_string
                                                                    us in
                                                                    let uu___32
                                                                    =
                                                                    FStar_Syntax_Print.univ_names_to_string
                                                                    act1.FStar_Syntax_Syntax.action_univs in
                                                                    FStar_Compiler_Util.format4
                                                                    "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                    uu___29
                                                                    uu___30
                                                                    uu___31
                                                                    uu___32 in
                                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                                    uu___28) in
                                                                  FStar_Errors.raise_error
                                                                    uu___27 r)) in
                                                      act2))))))))) in
                           let reify_sigelt =
                             if
                               FStar_Compiler_List.contains
                                 FStar_Syntax_Syntax.Reifiable quals
                             then
                               let env = env0 in
                               let r =
                                 FStar_Ident.range_of_lid
                                   ed.FStar_Syntax_Syntax.mname in
                               let uu___11 = fresh_a_and_u_a "a" in
                               match uu___11 with
                               | (a, u_a) ->
                                   let rest_bs =
                                     let signature_ts =
                                       let uu___12 = signature in
                                       match uu___12 with
                                       | (us, t, uu___13) -> (us, t) in
                                     let uu___12 =
                                       FStar_Compiler_Effect.op_Bar_Greater
                                         a.FStar_Syntax_Syntax.binder_bv
                                         FStar_Syntax_Syntax.bv_to_name in
                                     FStar_TypeChecker_Util.layered_effect_indices_as_binders
                                       env r ed.FStar_Syntax_Syntax.mname
                                       signature_ts u_a uu___12 in
                                   let f_binder =
                                     let thunked_t =
                                       let uu___12 =
                                         let uu___13 =
                                           let uu___14 =
                                             FStar_Syntax_Syntax.null_bv
                                               FStar_Syntax_Syntax.t_unit in
                                           FStar_Compiler_Effect.op_Bar_Greater
                                             uu___14
                                             FStar_Syntax_Syntax.mk_binder in
                                         [uu___13] in
                                       let uu___13 =
                                         let uu___14 =
                                           let uu___15 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               a.FStar_Syntax_Syntax.binder_bv in
                                           let uu___16 =
                                             FStar_Compiler_Effect.op_Bar_Greater
                                               rest_bs
                                               (FStar_Compiler_List.map
                                                  (fun b ->
                                                     let uu___17 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b.FStar_Syntax_Syntax.binder_bv in
                                                     FStar_Syntax_Syntax.as_arg
                                                       uu___17)) in
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               [];
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               uu___15;
                                             FStar_Syntax_Syntax.effect_args
                                               = uu___16;
                                             FStar_Syntax_Syntax.flags = []
                                           } in
                                         FStar_Compiler_Effect.op_Bar_Greater
                                           uu___14
                                           FStar_Syntax_Syntax.mk_Comp in
                                       FStar_Syntax_Util.arrow uu___12
                                         uu___13 in
                                     let uu___12 =
                                       FStar_Syntax_Syntax.null_bv thunked_t in
                                     FStar_Syntax_Syntax.mk_binder_with_attrs
                                       uu___12
                                       (FStar_Pervasives_Native.Some
                                          FStar_Syntax_Syntax.Equality) [] in
                                   let bs = a :: rest_bs in
                                   let applied_repr =
                                     let repr_ts =
                                       let uu___12 = repr in
                                       match uu___12 with
                                       | (us, t, uu___13) -> (us, t) in
                                     let repr1 =
                                       let uu___12 =
                                         FStar_TypeChecker_Env.inst_tscheme_with
                                           repr_ts [u_a] in
                                       FStar_Compiler_Effect.op_Bar_Greater
                                         uu___12 FStar_Pervasives_Native.snd in
                                     let uu___12 =
                                       FStar_Compiler_Effect.op_Bar_Greater
                                         bs
                                         (FStar_Compiler_List.map
                                            (fun b ->
                                               let uu___13 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   b.FStar_Syntax_Syntax.binder_bv in
                                               let uu___14 =
                                                 FStar_Syntax_Util.aqual_of_binder
                                                   b in
                                               (uu___13, uu___14))) in
                                     FStar_Syntax_Syntax.mk_Tm_app repr1
                                       uu___12 r in
                                   let reify_val_t =
                                     let bs1 =
                                       FStar_Compiler_Effect.op_Bar_Greater
                                         bs
                                         (FStar_Compiler_List.map
                                            (fun b ->
                                               {
                                                 FStar_Syntax_Syntax.binder_bv
                                                   =
                                                   (b.FStar_Syntax_Syntax.binder_bv);
                                                 FStar_Syntax_Syntax.binder_qual
                                                   =
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         false));
                                                 FStar_Syntax_Syntax.binder_attrs
                                                   = []
                                               })) in
                                     let uu___12 =
                                       if
                                         FStar_Compiler_List.contains
                                           FStar_Syntax_Syntax.TotalEffect
                                           quals
                                       then
                                         FStar_Syntax_Syntax.mk_Total
                                           applied_repr
                                       else
                                         FStar_Compiler_Effect.op_Bar_Greater
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               [];
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               FStar_Parser_Const.effect_Dv_lid;
                                             FStar_Syntax_Syntax.result_typ =
                                               applied_repr;
                                             FStar_Syntax_Syntax.effect_args
                                               = [];
                                             FStar_Syntax_Syntax.flags = []
                                           } FStar_Syntax_Syntax.mk_Comp in
                                     FStar_Syntax_Util.arrow
                                       (FStar_Compiler_List.op_At bs1
                                          [f_binder]) uu___12 in
                                   let uu___12 =
                                     FStar_TypeChecker_Generalize.generalize_universes
                                       env reify_val_t in
                                   (match uu___12 with
                                    | (us, reify_val_t1) ->
                                        let sig_assume_reify =
                                          let lid =
                                            FStar_Parser_Const.layered_effect_reify_val_lid
                                              ed.FStar_Syntax_Syntax.mname r in
                                          {
                                            FStar_Syntax_Syntax.sigel =
                                              (FStar_Syntax_Syntax.Sig_declare_typ
                                                 (lid, us, reify_val_t1));
                                            FStar_Syntax_Syntax.sigrng = r;
                                            FStar_Syntax_Syntax.sigquals =
                                              [FStar_Syntax_Syntax.Assumption];
                                            FStar_Syntax_Syntax.sigmeta =
                                              FStar_Syntax_Syntax.default_sigmeta;
                                            FStar_Syntax_Syntax.sigattrs = [];
                                            FStar_Syntax_Syntax.sigopts =
                                              FStar_Pervasives_Native.None
                                          } in
                                        ((let uu___14 =
                                            let uu___15 =
                                              let uu___16 =
                                                FStar_Ident.string_of_lid
                                                  ed.FStar_Syntax_Syntax.mname in
                                              FStar_Compiler_Util.format1
                                                "Reification of indexed effects (%s here) is supported only as a type coercion to the underlying representation type (no support for smt-based reasoning or extraction)"
                                                uu___16 in
                                            (FStar_Errors.Warning_BleedingEdge_Feature,
                                              uu___15) in
                                          FStar_Errors.log_issue r uu___14);
                                         [sig_assume_reify]))
                             else [] in
                           let tschemes_of uu___11 k =
                             match uu___11 with
                             | (us, t, ty) -> ((us, t), (us, ty), k) in
                           let combinators =
                             FStar_Syntax_Syntax.Layered_eff
                               {
                                 FStar_Syntax_Syntax.l_repr =
                                   (tschemes_of repr
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Syntax.Standard_combinator
                                            [])));
                                 FStar_Syntax_Syntax.l_return =
                                   (tschemes_of return_repr
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Ad_hoc_combinator));
                                 FStar_Syntax_Syntax.l_bind =
                                   (tschemes_of bind_repr
                                      (FStar_Pervasives_Native.Some
                                         bind_combinator_kind1));
                                 FStar_Syntax_Syntax.l_subcomp =
                                   (tschemes_of stronger_repr
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Ad_hoc_combinator));
                                 FStar_Syntax_Syntax.l_if_then_else =
                                   (tschemes_of if_then_else
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Ad_hoc_combinator))
                               } in
                           let uu___11 =
                             let uu___12 =
                               FStar_Compiler_List.map (tc_action env0)
                                 ed.FStar_Syntax_Syntax.actions in
                             {
                               FStar_Syntax_Syntax.mname =
                                 (ed.FStar_Syntax_Syntax.mname);
                               FStar_Syntax_Syntax.cattributes =
                                 (ed.FStar_Syntax_Syntax.cattributes);
                               FStar_Syntax_Syntax.univs =
                                 (ed.FStar_Syntax_Syntax.univs);
                               FStar_Syntax_Syntax.binders =
                                 (ed.FStar_Syntax_Syntax.binders);
                               FStar_Syntax_Syntax.signature =
                                 (let uu___13 = signature in
                                  match uu___13 with
                                  | (us, t, uu___14) -> (us, t));
                               FStar_Syntax_Syntax.combinators = combinators;
                               FStar_Syntax_Syntax.actions = uu___12;
                               FStar_Syntax_Syntax.eff_attrs =
                                 (ed.FStar_Syntax_Syntax.eff_attrs)
                             } in
                           (uu___11, reify_sigelt))))))))))
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          FStar_Syntax_Syntax.eff_decl)
  =
  fun env0 ->
    fun ed ->
      fun _quals ->
        fun _attrs ->
          let uu___ =
            let uu___1 =
              FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
            FStar_Compiler_Util.format1
              "While checking effect definition `%s`" uu___1 in
          FStar_Errors.with_ctx uu___
            (fun uu___1 ->
               (let uu___3 =
                  FStar_Compiler_Effect.op_Less_Bar
                    (FStar_TypeChecker_Env.debug env0)
                    (FStar_Options.Other "ED") in
                if uu___3
                then
                  let uu___4 = FStar_Syntax_Print.eff_decl_to_string false ed in
                  FStar_Compiler_Util.print1
                    "Typechecking eff_decl: \n\t%s\n" uu___4
                else ());
               (let uu___3 =
                  let uu___4 =
                    FStar_Syntax_Subst.univ_var_opening
                      ed.FStar_Syntax_Syntax.univs in
                  match uu___4 with
                  | (ed_univs_subst, ed_univs) ->
                      let bs =
                        let uu___5 =
                          FStar_Syntax_Subst.subst_binders ed_univs_subst
                            ed.FStar_Syntax_Syntax.binders in
                        FStar_Syntax_Subst.open_binders uu___5 in
                      let uu___5 =
                        let uu___6 =
                          FStar_TypeChecker_Env.push_univ_vars env0 ed_univs in
                        FStar_TypeChecker_TcTerm.tc_tparams uu___6 bs in
                      (match uu___5 with
                       | (bs1, uu___6, uu___7) ->
                           let uu___8 =
                             let tmp_t =
                               let uu___9 =
                                 let uu___10 =
                                   FStar_Compiler_Effect.op_Bar_Greater
                                     FStar_Syntax_Syntax.U_zero
                                     (fun uu___11 ->
                                        FStar_Pervasives_Native.Some uu___11) in
                                 FStar_Syntax_Syntax.mk_Total'
                                   FStar_Syntax_Syntax.t_unit uu___10 in
                               FStar_Syntax_Util.arrow bs1 uu___9 in
                             let uu___9 =
                               FStar_TypeChecker_Generalize.generalize_universes
                                 env0 tmp_t in
                             match uu___9 with
                             | (us, tmp_t1) ->
                                 let uu___10 =
                                   let uu___11 =
                                     let uu___12 =
                                       FStar_Compiler_Effect.op_Bar_Greater
                                         tmp_t1
                                         FStar_Syntax_Util.arrow_formals in
                                     FStar_Compiler_Effect.op_Bar_Greater
                                       uu___12 FStar_Pervasives_Native.fst in
                                   FStar_Compiler_Effect.op_Bar_Greater
                                     uu___11 FStar_Syntax_Subst.close_binders in
                                 (us, uu___10) in
                           (match uu___8 with
                            | (us, bs2) ->
                                (match ed_univs with
                                 | [] -> (us, bs2)
                                 | uu___9 ->
                                     let uu___10 =
                                       ((FStar_Compiler_List.length ed_univs)
                                          = (FStar_Compiler_List.length us))
                                         &&
                                         (FStar_Compiler_List.forall2
                                            (fun u1 ->
                                               fun u2 ->
                                                 let uu___11 =
                                                   FStar_Syntax_Syntax.order_univ_name
                                                     u1 u2 in
                                                 uu___11 = Prims.int_zero)
                                            ed_univs us) in
                                     if uu___10
                                     then (us, bs2)
                                     else
                                       (let uu___12 =
                                          let uu___13 =
                                            let uu___14 =
                                              FStar_Ident.string_of_lid
                                                ed.FStar_Syntax_Syntax.mname in
                                            let uu___15 =
                                              FStar_Compiler_Util.string_of_int
                                                (FStar_Compiler_List.length
                                                   ed_univs) in
                                            let uu___16 =
                                              FStar_Compiler_Util.string_of_int
                                                (FStar_Compiler_List.length
                                                   us) in
                                            FStar_Compiler_Util.format3
                                              "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                              uu___14 uu___15 uu___16 in
                                          (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                            uu___13) in
                                        let uu___13 =
                                          FStar_Ident.range_of_lid
                                            ed.FStar_Syntax_Syntax.mname in
                                        FStar_Errors.raise_error uu___12
                                          uu___13)))) in
                match uu___3 with
                | (us, bs) ->
                    let ed1 =
                      {
                        FStar_Syntax_Syntax.mname =
                          (ed.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.cattributes =
                          (ed.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.univs = us;
                        FStar_Syntax_Syntax.binders = bs;
                        FStar_Syntax_Syntax.signature =
                          (ed.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.combinators =
                          (ed.FStar_Syntax_Syntax.combinators);
                        FStar_Syntax_Syntax.actions =
                          (ed.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (ed.FStar_Syntax_Syntax.eff_attrs)
                      } in
                    let uu___4 = FStar_Syntax_Subst.univ_var_opening us in
                    (match uu___4 with
                     | (ed_univs_subst, ed_univs) ->
                         let uu___5 =
                           let uu___6 =
                             FStar_Syntax_Subst.subst_binders ed_univs_subst
                               bs in
                           FStar_Syntax_Subst.open_binders' uu___6 in
                         (match uu___5 with
                          | (ed_bs, ed_bs_subst) ->
                              let ed2 =
                                let op uu___6 =
                                  match uu___6 with
                                  | (us1, t) ->
                                      let t1 =
                                        let uu___7 =
                                          FStar_Syntax_Subst.shift_subst
                                            ((FStar_Compiler_List.length
                                                ed_bs)
                                               +
                                               (FStar_Compiler_List.length
                                                  us1)) ed_univs_subst in
                                        FStar_Syntax_Subst.subst uu___7 t in
                                      let uu___7 =
                                        let uu___8 =
                                          FStar_Syntax_Subst.shift_subst
                                            (FStar_Compiler_List.length us1)
                                            ed_bs_subst in
                                        FStar_Syntax_Subst.subst uu___8 t1 in
                                      (us1, uu___7) in
                                let uu___6 =
                                  op ed1.FStar_Syntax_Syntax.signature in
                                let uu___7 =
                                  FStar_Syntax_Util.apply_eff_combinators op
                                    ed1.FStar_Syntax_Syntax.combinators in
                                let uu___8 =
                                  FStar_Compiler_List.map
                                    (fun a ->
                                       let uu___9 =
                                         let uu___10 =
                                           op
                                             ((a.FStar_Syntax_Syntax.action_univs),
                                               (a.FStar_Syntax_Syntax.action_defn)) in
                                         FStar_Pervasives_Native.snd uu___10 in
                                       let uu___10 =
                                         let uu___11 =
                                           op
                                             ((a.FStar_Syntax_Syntax.action_univs),
                                               (a.FStar_Syntax_Syntax.action_typ)) in
                                         FStar_Pervasives_Native.snd uu___11 in
                                       {
                                         FStar_Syntax_Syntax.action_name =
                                           (a.FStar_Syntax_Syntax.action_name);
                                         FStar_Syntax_Syntax.action_unqualified_name
                                           =
                                           (a.FStar_Syntax_Syntax.action_unqualified_name);
                                         FStar_Syntax_Syntax.action_univs =
                                           (a.FStar_Syntax_Syntax.action_univs);
                                         FStar_Syntax_Syntax.action_params =
                                           (a.FStar_Syntax_Syntax.action_params);
                                         FStar_Syntax_Syntax.action_defn =
                                           uu___9;
                                         FStar_Syntax_Syntax.action_typ =
                                           uu___10
                                       }) ed1.FStar_Syntax_Syntax.actions in
                                {
                                  FStar_Syntax_Syntax.mname =
                                    (ed1.FStar_Syntax_Syntax.mname);
                                  FStar_Syntax_Syntax.cattributes =
                                    (ed1.FStar_Syntax_Syntax.cattributes);
                                  FStar_Syntax_Syntax.univs =
                                    (ed1.FStar_Syntax_Syntax.univs);
                                  FStar_Syntax_Syntax.binders =
                                    (ed1.FStar_Syntax_Syntax.binders);
                                  FStar_Syntax_Syntax.signature = uu___6;
                                  FStar_Syntax_Syntax.combinators = uu___7;
                                  FStar_Syntax_Syntax.actions = uu___8;
                                  FStar_Syntax_Syntax.eff_attrs =
                                    (ed1.FStar_Syntax_Syntax.eff_attrs)
                                } in
                              ((let uu___7 =
                                  FStar_Compiler_Effect.op_Less_Bar
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED") in
                                if uu___7
                                then
                                  let uu___8 =
                                    FStar_Syntax_Print.eff_decl_to_string
                                      false ed2 in
                                  FStar_Compiler_Util.print1
                                    "After typechecking binders eff_decl: \n\t%s\n"
                                    uu___8
                                else ());
                               (let env =
                                  let uu___7 =
                                    FStar_TypeChecker_Env.push_univ_vars env0
                                      ed_univs in
                                  FStar_TypeChecker_Env.push_binders uu___7
                                    ed_bs in
                                let check_and_gen' comb n env_opt uu___7 k =
                                  match uu___7 with
                                  | (us1, t) ->
                                      let env1 =
                                        if
                                          FStar_Compiler_Util.is_some env_opt
                                        then
                                          FStar_Compiler_Effect.op_Bar_Greater
                                            env_opt FStar_Compiler_Util.must
                                        else env in
                                      let uu___8 =
                                        FStar_Syntax_Subst.open_univ_vars us1
                                          t in
                                      (match uu___8 with
                                       | (us2, t1) ->
                                           let t2 =
                                             match k with
                                             | FStar_Pervasives_Native.Some
                                                 k1 ->
                                                 let uu___9 =
                                                   FStar_TypeChecker_Env.push_univ_vars
                                                     env1 us2 in
                                                 FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                                   uu___9 t1 k1
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 let uu___9 =
                                                   let uu___10 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env1 us2 in
                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                     uu___10 t1 in
                                                 (match uu___9 with
                                                  | (t3, uu___10, g) ->
                                                      (FStar_TypeChecker_Rel.force_trivial_guard
                                                         env1 g;
                                                       t3)) in
                                           let uu___9 =
                                             FStar_TypeChecker_Generalize.generalize_universes
                                               env1 t2 in
                                           (match uu___9 with
                                            | (g_us, t3) ->
                                                (if
                                                   (FStar_Compiler_List.length
                                                      g_us)
                                                     <> n
                                                 then
                                                   (let error =
                                                      let uu___11 =
                                                        FStar_Ident.string_of_lid
                                                          ed2.FStar_Syntax_Syntax.mname in
                                                      let uu___12 =
                                                        FStar_Compiler_Util.string_of_int
                                                          n in
                                                      let uu___13 =
                                                        let uu___14 =
                                                          FStar_Compiler_Effect.op_Bar_Greater
                                                            g_us
                                                            FStar_Compiler_List.length in
                                                        FStar_Compiler_Effect.op_Bar_Greater
                                                          uu___14
                                                          FStar_Compiler_Util.string_of_int in
                                                      FStar_Compiler_Util.format4
                                                        "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                        uu___11 comb uu___12
                                                        uu___13 in
                                                    FStar_Errors.raise_error
                                                      (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                        error)
                                                      t3.FStar_Syntax_Syntax.pos)
                                                 else ();
                                                 (match us2 with
                                                  | [] -> (g_us, t3)
                                                  | uu___11 ->
                                                      let uu___12 =
                                                        ((FStar_Compiler_List.length
                                                            us2)
                                                           =
                                                           (FStar_Compiler_List.length
                                                              g_us))
                                                          &&
                                                          (FStar_Compiler_List.forall2
                                                             (fun u1 ->
                                                                fun u2 ->
                                                                  let uu___13
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2 in
                                                                  uu___13 =
                                                                    Prims.int_zero)
                                                             us2 g_us) in
                                                      if uu___12
                                                      then (g_us, t3)
                                                      else
                                                        (let uu___14 =
                                                           let uu___15 =
                                                             let uu___16 =
                                                               FStar_Ident.string_of_lid
                                                                 ed2.FStar_Syntax_Syntax.mname in
                                                             let uu___17 =
                                                               FStar_Compiler_Util.string_of_int
                                                                 (FStar_Compiler_List.length
                                                                    us2) in
                                                             let uu___18 =
                                                               FStar_Compiler_Util.string_of_int
                                                                 (FStar_Compiler_List.length
                                                                    g_us) in
                                                             FStar_Compiler_Util.format4
                                                               "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                               uu___16 comb
                                                               uu___17
                                                               uu___18 in
                                                           (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                             uu___15) in
                                                         FStar_Errors.raise_error
                                                           uu___14
                                                           t3.FStar_Syntax_Syntax.pos))))) in
                                let signature =
                                  check_and_gen' "signature" Prims.int_one
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                    FStar_Pervasives_Native.None in
                                (let uu___8 =
                                   FStar_Compiler_Effect.op_Less_Bar
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "ED") in
                                 if uu___8
                                 then
                                   let uu___9 =
                                     FStar_Syntax_Print.tscheme_to_string
                                       signature in
                                   FStar_Compiler_Util.print1
                                     "Typechecked signature: %s\n" uu___9
                                 else ());
                                (let fresh_a_and_wp uu___8 =
                                   let fail t =
                                     let uu___9 =
                                       FStar_TypeChecker_Err.unexpected_signature_for_monad
                                         env ed2.FStar_Syntax_Syntax.mname t in
                                     FStar_Errors.raise_error uu___9
                                       (FStar_Pervasives_Native.snd
                                          ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                                   let uu___9 =
                                     FStar_TypeChecker_Env.inst_tscheme
                                       signature in
                                   match uu___9 with
                                   | (uu___10, signature1) ->
                                       let uu___11 =
                                         let uu___12 =
                                           FStar_Syntax_Subst.compress
                                             signature1 in
                                         uu___12.FStar_Syntax_Syntax.n in
                                       (match uu___11 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs1, uu___12) ->
                                            let bs2 =
                                              FStar_Syntax_Subst.open_binders
                                                bs1 in
                                            (match bs2 with
                                             | {
                                                 FStar_Syntax_Syntax.binder_bv
                                                   = a;
                                                 FStar_Syntax_Syntax.binder_qual
                                                   = uu___13;
                                                 FStar_Syntax_Syntax.binder_attrs
                                                   = uu___14;_}::{
                                                                   FStar_Syntax_Syntax.binder_bv
                                                                    = wp;
                                                                   FStar_Syntax_Syntax.binder_qual
                                                                    = uu___15;
                                                                   FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___16;_}::[]
                                                 ->
                                                 (a,
                                                   (wp.FStar_Syntax_Syntax.sort))
                                             | uu___13 -> fail signature1)
                                        | uu___12 -> fail signature1) in
                                 let log_combinator s ts =
                                   let uu___8 =
                                     FStar_Compiler_Effect.op_Less_Bar
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "ED") in
                                   if uu___8
                                   then
                                     let uu___9 =
                                       FStar_Ident.string_of_lid
                                         ed2.FStar_Syntax_Syntax.mname in
                                     let uu___10 =
                                       FStar_Syntax_Print.tscheme_to_string
                                         ts in
                                     FStar_Compiler_Util.print3
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
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu___11 =
                                             let uu___12 =
                                               let uu___13 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   a in
                                               FStar_Syntax_Syntax.null_binder
                                                 uu___13 in
                                             [uu___12] in
                                           uu___10 :: uu___11 in
                                         let uu___10 =
                                           FStar_Syntax_Syntax.mk_GTotal
                                             wp_sort in
                                         FStar_Syntax_Util.arrow uu___9
                                           uu___10 in
                                       let uu___9 =
                                         FStar_Compiler_Effect.op_Bar_Greater
                                           ed2
                                           FStar_Syntax_Util.get_return_vc_combinator in
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
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu___13 in
                                                 [uu___12] in
                                               let uu___12 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   wp_sort_b in
                                               FStar_Syntax_Util.arrow
                                                 uu___11 uu___12 in
                                             let k =
                                               let uu___11 =
                                                 let uu___12 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     a in
                                                 let uu___13 =
                                                   let uu___14 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       b in
                                                   let uu___15 =
                                                     let uu___16 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         wp_sort_a in
                                                     let uu___17 =
                                                       let uu___18 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a_b in
                                                       [uu___18] in
                                                     uu___16 :: uu___17 in
                                                   uu___14 :: uu___15 in
                                                 uu___12 :: uu___13 in
                                               let uu___12 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   wp_sort_b in
                                               FStar_Syntax_Util.arrow
                                                 uu___11 uu___12 in
                                             let uu___11 =
                                               let uu___12 =
                                                 FStar_Compiler_Effect.op_Bar_Greater
                                                   ed2
                                                   FStar_Syntax_Util.get_bind_vc_combinator in
                                               FStar_Compiler_Effect.op_Bar_Greater
                                                 uu___12
                                                 FStar_Pervasives_Native.fst in
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
                                           FStar_Syntax_Util.type_u () in
                                         (match uu___11 with
                                          | (t, uu___12) ->
                                              let k =
                                                let uu___13 =
                                                  let uu___14 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a in
                                                  let uu___15 =
                                                    let uu___16 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a in
                                                    let uu___17 =
                                                      let uu___18 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          wp_sort_a in
                                                      [uu___18] in
                                                    uu___16 :: uu___17 in
                                                  uu___14 :: uu___15 in
                                                let uu___14 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    t in
                                                FStar_Syntax_Util.arrow
                                                  uu___13 uu___14 in
                                              let uu___13 =
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  ed2
                                                  FStar_Syntax_Util.get_stronger_vc_combinator in
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
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname in
                                              FStar_Pervasives_Native.Some
                                                uu___13 in
                                            let uu___13 =
                                              let uu___14 =
                                                FStar_Syntax_Util.type_u () in
                                              FStar_Compiler_Effect.op_Bar_Greater
                                                uu___14
                                                FStar_Pervasives_Native.fst in
                                            FStar_Syntax_Syntax.new_bv
                                              uu___12 uu___13 in
                                          let k =
                                            let uu___12 =
                                              let uu___13 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a in
                                              let uu___14 =
                                                let uu___15 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    p in
                                                let uu___16 =
                                                  let uu___17 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a in
                                                  let uu___18 =
                                                    let uu___19 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a in
                                                    [uu___19] in
                                                  uu___17 :: uu___18 in
                                                uu___15 :: uu___16 in
                                              uu___13 :: uu___14 in
                                            let uu___13 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a in
                                            FStar_Syntax_Util.arrow uu___12
                                              uu___13 in
                                          let uu___12 =
                                            let uu___13 =
                                              FStar_Compiler_Effect.op_Bar_Greater
                                                ed2
                                                FStar_Syntax_Util.get_wp_if_then_else_combinator in
                                            FStar_Compiler_Effect.op_Bar_Greater
                                              uu___13
                                              FStar_Compiler_Util.must in
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
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a in
                                               let uu___15 =
                                                 let uu___16 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a in
                                                 [uu___16] in
                                               uu___14 :: uu___15 in
                                             let uu___14 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 wp_sort_a in
                                             FStar_Syntax_Util.arrow uu___13
                                               uu___14 in
                                           let uu___13 =
                                             let uu___14 =
                                               FStar_Compiler_Effect.op_Bar_Greater
                                                 ed2
                                                 FStar_Syntax_Util.get_wp_ite_combinator in
                                             FStar_Compiler_Effect.op_Bar_Greater
                                               uu___14
                                               FStar_Compiler_Util.must in
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
                                                  FStar_Ident.range_of_lid
                                                    ed2.FStar_Syntax_Syntax.mname in
                                                FStar_Pervasives_Native.Some
                                                  uu___15 in
                                              let uu___15 =
                                                let uu___16 =
                                                  FStar_Syntax_Util.type_u () in
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  uu___16
                                                  FStar_Pervasives_Native.fst in
                                              FStar_Syntax_Syntax.new_bv
                                                uu___14 uu___15 in
                                            let wp_sort_b_a =
                                              let uu___14 =
                                                let uu___15 =
                                                  let uu___16 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      b in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu___16 in
                                                [uu___15] in
                                              let uu___15 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a in
                                              FStar_Syntax_Util.arrow uu___14
                                                uu___15 in
                                            let k =
                                              let uu___14 =
                                                let uu___15 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu___16 =
                                                  let uu___17 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b in
                                                  let uu___18 =
                                                    let uu___19 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_b_a in
                                                    [uu___19] in
                                                  uu___17 :: uu___18 in
                                                uu___15 :: uu___16 in
                                              let uu___15 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a in
                                              FStar_Syntax_Util.arrow uu___14
                                                uu___15 in
                                            let uu___14 =
                                              let uu___15 =
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  ed2
                                                  FStar_Syntax_Util.get_wp_close_combinator in
                                              FStar_Compiler_Effect.op_Bar_Greater
                                                uu___15
                                                FStar_Compiler_Util.must in
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
                                               FStar_Syntax_Util.type_u () in
                                             (match uu___15 with
                                              | (t, uu___16) ->
                                                  let k =
                                                    let uu___17 =
                                                      let uu___18 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a in
                                                      let uu___19 =
                                                        let uu___20 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            wp_sort_a in
                                                        [uu___20] in
                                                      uu___18 :: uu___19 in
                                                    let uu___18 =
                                                      FStar_Syntax_Syntax.mk_GTotal
                                                        t in
                                                    FStar_Syntax_Util.arrow
                                                      uu___17 uu___18 in
                                                  let trivial1 =
                                                    let uu___17 =
                                                      let uu___18 =
                                                        FStar_Compiler_Effect.op_Bar_Greater
                                                          ed2
                                                          FStar_Syntax_Util.get_wp_trivial_combinator in
                                                      FStar_Compiler_Effect.op_Bar_Greater
                                                        uu___18
                                                        FStar_Compiler_Util.must in
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
                                           FStar_Compiler_Effect.op_Bar_Greater
                                             ed2
                                             FStar_Syntax_Util.get_eff_repr in
                                         match uu___15 with
                                         | FStar_Pervasives_Native.None ->
                                             (FStar_Pervasives_Native.None,
                                               FStar_Pervasives_Native.None,
                                               FStar_Pervasives_Native.None,
                                               (ed2.FStar_Syntax_Syntax.actions))
                                         | uu___16 ->
                                             let repr =
                                               let uu___17 =
                                                 fresh_a_and_wp () in
                                               match uu___17 with
                                               | (a, wp_sort_a) ->
                                                   let uu___18 =
                                                     FStar_Syntax_Util.type_u
                                                       () in
                                                   (match uu___18 with
                                                    | (t, uu___19) ->
                                                        let k =
                                                          let uu___20 =
                                                            let uu___21 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                a in
                                                            let uu___22 =
                                                              let uu___23 =
                                                                FStar_Syntax_Syntax.null_binder
                                                                  wp_sort_a in
                                                              [uu___23] in
                                                            uu___21 ::
                                                              uu___22 in
                                                          let uu___21 =
                                                            FStar_Syntax_Syntax.mk_GTotal
                                                              t in
                                                          FStar_Syntax_Util.arrow
                                                            uu___20 uu___21 in
                                                        let uu___20 =
                                                          let uu___21 =
                                                            FStar_Compiler_Effect.op_Bar_Greater
                                                              ed2
                                                              FStar_Syntax_Util.get_eff_repr in
                                                          FStar_Compiler_Effect.op_Bar_Greater
                                                            uu___21
                                                            FStar_Compiler_Util.must in
                                                        check_and_gen' "repr"
                                                          Prims.int_one
                                                          FStar_Pervasives_Native.None
                                                          uu___20
                                                          (FStar_Pervasives_Native.Some
                                                             k)) in
                                             (log_combinator "repr" repr;
                                              (let mk_repr' t wp =
                                                 let uu___18 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     repr in
                                                 match uu___18 with
                                                 | (uu___19, repr1) ->
                                                     let repr2 =
                                                       FStar_TypeChecker_Normalize.normalize
                                                         [FStar_TypeChecker_Env.EraseUniverses;
                                                         FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                         env repr1 in
                                                     let uu___20 =
                                                       let uu___21 =
                                                         let uu___22 =
                                                           let uu___23 =
                                                             FStar_Compiler_Effect.op_Bar_Greater
                                                               t
                                                               FStar_Syntax_Syntax.as_arg in
                                                           let uu___24 =
                                                             let uu___25 =
                                                               FStar_Compiler_Effect.op_Bar_Greater
                                                                 wp
                                                                 FStar_Syntax_Syntax.as_arg in
                                                             [uu___25] in
                                                           uu___23 :: uu___24 in
                                                         (repr2, uu___22) in
                                                       FStar_Syntax_Syntax.Tm_app
                                                         uu___21 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu___20
                                                       FStar_Compiler_Range.dummyRange in
                                               let mk_repr a wp =
                                                 let uu___18 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a in
                                                 mk_repr' uu___18 wp in
                                               let destruct_repr t =
                                                 let uu___18 =
                                                   let uu___19 =
                                                     FStar_Syntax_Subst.compress
                                                       t in
                                                   uu___19.FStar_Syntax_Syntax.n in
                                                 match uu___18 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu___19,
                                                      (t1, uu___20)::
                                                      (wp, uu___21)::[])
                                                     -> (t1, wp)
                                                 | uu___19 ->
                                                     failwith
                                                       "Unexpected repr type" in
                                               let return_repr =
                                                 let return_repr_ts =
                                                   let uu___18 =
                                                     FStar_Compiler_Effect.op_Bar_Greater
                                                       ed2
                                                       FStar_Syntax_Util.get_return_repr in
                                                   FStar_Compiler_Effect.op_Bar_Greater
                                                     uu___18
                                                     FStar_Compiler_Util.must in
                                                 let uu___18 =
                                                   fresh_a_and_wp () in
                                                 match uu___18 with
                                                 | (a, uu___19) ->
                                                     let x_a =
                                                       let uu___20 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "x_a"
                                                         FStar_Pervasives_Native.None
                                                         uu___20 in
                                                     let res =
                                                       let wp =
                                                         let uu___20 =
                                                           let uu___21 =
                                                             FStar_TypeChecker_Env.inst_tscheme
                                                               ret_wp in
                                                           FStar_Compiler_Effect.op_Bar_Greater
                                                             uu___21
                                                             FStar_Pervasives_Native.snd in
                                                         let uu___21 =
                                                           let uu___22 =
                                                             let uu___23 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 a in
                                                             FStar_Compiler_Effect.op_Bar_Greater
                                                               uu___23
                                                               FStar_Syntax_Syntax.as_arg in
                                                           let uu___23 =
                                                             let uu___24 =
                                                               let uu___25 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   x_a in
                                                               FStar_Compiler_Effect.op_Bar_Greater
                                                                 uu___25
                                                                 FStar_Syntax_Syntax.as_arg in
                                                             [uu___24] in
                                                           uu___22 :: uu___23 in
                                                         FStar_Syntax_Syntax.mk_Tm_app
                                                           uu___20 uu___21
                                                           FStar_Compiler_Range.dummyRange in
                                                       mk_repr a wp in
                                                     let k =
                                                       let uu___20 =
                                                         let uu___21 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             a in
                                                         let uu___22 =
                                                           let uu___23 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu___23] in
                                                         uu___21 :: uu___22 in
                                                       let uu___21 =
                                                         FStar_Syntax_Syntax.mk_Total
                                                           res in
                                                       FStar_Syntax_Util.arrow
                                                         uu___20 uu___21 in
                                                     let uu___20 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env k in
                                                     (match uu___20 with
                                                      | (k1, uu___21,
                                                         uu___22) ->
                                                          let env1 =
                                                            let uu___23 =
                                                              FStar_TypeChecker_Env.set_range
                                                                env
                                                                (FStar_Pervasives_Native.snd
                                                                   return_repr_ts).FStar_Syntax_Syntax.pos in
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
                                                      FStar_Compiler_Effect.op_Bar_Greater
                                                        ed2
                                                        FStar_Syntax_Util.get_bind_repr in
                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                      uu___19
                                                      FStar_Compiler_Util.must in
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
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                 FStar_Syntax_Syntax.null_binder
                                                                   uu___23 in
                                                               [uu___22] in
                                                             let uu___22 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 wp_sort_b in
                                                             FStar_Syntax_Util.arrow
                                                               uu___21
                                                               uu___22 in
                                                           let wp_f =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp_f"
                                                               FStar_Pervasives_Native.None
                                                               wp_sort_a in
                                                           let wp_g =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp_g"
                                                               FStar_Pervasives_Native.None
                                                               wp_sort_a_b in
                                                           let x_a =
                                                             let uu___21 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 a in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "x_a"
                                                               FStar_Pervasives_Native.None
                                                               uu___21 in
                                                           let wp_g_x =
                                                             let uu___21 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_g in
                                                             let uu___22 =
                                                               let uu___23 =
                                                                 let uu___24
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    x_a in
                                                                 FStar_Compiler_Effect.op_Bar_Greater
                                                                   uu___24
                                                                   FStar_Syntax_Syntax.as_arg in
                                                               [uu___23] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               uu___21
                                                               uu___22
                                                               FStar_Compiler_Range.dummyRange in
                                                           let res =
                                                             let wp =
                                                               let uu___21 =
                                                                 let uu___22
                                                                   =
                                                                   FStar_TypeChecker_Env.inst_tscheme
                                                                    bind_wp in
                                                                 FStar_Compiler_Effect.op_Bar_Greater
                                                                   uu___22
                                                                   FStar_Pervasives_Native.snd in
                                                               let uu___22 =
                                                                 let uu___23
                                                                   =
                                                                   let uu___24
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                   let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
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
                                                                 FStar_Compiler_List.map
                                                                   FStar_Syntax_Syntax.as_arg
                                                                   uu___23 in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu___21
                                                                 uu___22
                                                                 FStar_Compiler_Range.dummyRange in
                                                             mk_repr b wp in
                                                           let maybe_range_arg
                                                             =
                                                             let uu___21 =
                                                               FStar_Compiler_Util.for_some
                                                                 (FStar_Syntax_Util.attr_eq
                                                                    FStar_Syntax_Util.dm4f_bind_range_attr)
                                                                 ed2.FStar_Syntax_Syntax.eff_attrs in
                                                             if uu___21
                                                             then
                                                               let uu___22 =
                                                                 FStar_Syntax_Syntax.null_binder
                                                                   FStar_Syntax_Syntax.t_range in
                                                               let uu___23 =
                                                                 let uu___24
                                                                   =
                                                                   FStar_Syntax_Syntax.null_binder
                                                                    FStar_Syntax_Syntax.t_range in
                                                                 [uu___24] in
                                                               uu___22 ::
                                                                 uu___23
                                                             else [] in
                                                           let k =
                                                             let uu___21 =
                                                               let uu___22 =
                                                                 let uu___23
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_binder
                                                                    a in
                                                                 let uu___24
                                                                   =
                                                                   let uu___25
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    b in
                                                                   [uu___25] in
                                                                 uu___23 ::
                                                                   uu___24 in
                                                               let uu___23 =
                                                                 let uu___24
                                                                   =
                                                                   let uu___25
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp_f in
                                                                   let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    mk_repr a
                                                                    uu___29 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu___28 in
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
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
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                    [uu___34] in
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x in
                                                                    FStar_Compiler_Effect.op_Less_Bar
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu___35 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu___33
                                                                    uu___34 in
                                                                    FStar_Syntax_Syntax.null_binder
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
                                                                 FStar_Compiler_List.op_At
                                                                   maybe_range_arg
                                                                   uu___24 in
                                                               FStar_Compiler_List.op_At
                                                                 uu___22
                                                                 uu___23 in
                                                             let uu___22 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 res in
                                                             FStar_Syntax_Util.arrow
                                                               uu___21
                                                               uu___22 in
                                                           let uu___21 =
                                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                               env k in
                                                           (match uu___21
                                                            with
                                                            | (k1, uu___22,
                                                               uu___23) ->
                                                                let env1 =
                                                                  FStar_TypeChecker_Env.set_range
                                                                    env
                                                                    (FStar_Pervasives_Native.snd
                                                                    bind_repr_ts).FStar_Syntax_Syntax.pos in
                                                                let env2 =
                                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                                                    FStar_TypeChecker_Env.teq_nosmt_force
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                                                                    FStar_TypeChecker_Env.subtype_nosmt_force
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.erasable_types_tab);
                                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                                                                    FStar_TypeChecker_Env.unif_allow_ref_guards
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                                                    FStar_TypeChecker_Env.erase_erasable_args
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.erase_erasable_args);
                                                                    FStar_TypeChecker_Env.core_check
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.core_check)
                                                                    }
                                                                    (
                                                                    fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___24) in
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
                                                       (FStar_Compiler_List.length
                                                          act.FStar_Syntax_Syntax.action_params)
                                                         <> Prims.int_zero
                                                     then
                                                       failwith
                                                         "tc_eff_decl: expected action_params to be empty"
                                                     else ();
                                                     (let uu___21 =
                                                        if
                                                          act.FStar_Syntax_Syntax.action_univs
                                                            = []
                                                        then (env, act)
                                                        else
                                                          (let uu___23 =
                                                             FStar_Syntax_Subst.univ_var_opening
                                                               act.FStar_Syntax_Syntax.action_univs in
                                                           match uu___23 with
                                                           | (usubst, uvs) ->
                                                               let uu___24 =
                                                                 FStar_TypeChecker_Env.push_univ_vars
                                                                   env uvs in
                                                               let uu___25 =
                                                                 let uu___26
                                                                   =
                                                                   FStar_Syntax_Subst.subst
                                                                    usubst
                                                                    act.FStar_Syntax_Syntax.action_defn in
                                                                 let uu___27
                                                                   =
                                                                   FStar_Syntax_Subst.subst
                                                                    usubst
                                                                    act.FStar_Syntax_Syntax.action_typ in
                                                                 {
                                                                   FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (act.FStar_Syntax_Syntax.action_name);
                                                                   FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (act.FStar_Syntax_Syntax.action_unqualified_name);
                                                                   FStar_Syntax_Syntax.action_univs
                                                                    = uvs;
                                                                   FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (act.FStar_Syntax_Syntax.action_params);
                                                                   FStar_Syntax_Syntax.action_defn
                                                                    = uu___26;
                                                                   FStar_Syntax_Syntax.action_typ
                                                                    = uu___27
                                                                 } in
                                                               (uu___24,
                                                                 uu___25)) in
                                                      match uu___21 with
                                                      | (env1, act1) ->
                                                          let act_typ =
                                                            let uu___22 =
                                                              let uu___23 =
                                                                FStar_Syntax_Subst.compress
                                                                  act1.FStar_Syntax_Syntax.action_typ in
                                                              uu___23.FStar_Syntax_Syntax.n in
                                                            match uu___22
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_arrow
                                                                (bs1, c) ->
                                                                let c1 =
                                                                  FStar_Syntax_Util.comp_to_comp_typ
                                                                    c in
                                                                let uu___23 =
                                                                  FStar_Ident.lid_equals
                                                                    c1.FStar_Syntax_Syntax.effect_name
                                                                    ed2.FStar_Syntax_Syntax.mname in
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
                                                                    FStar_Compiler_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___27 in
                                                                    mk_repr'
                                                                    c1.FStar_Syntax_Syntax.result_typ
                                                                    uu___26 in
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu___25 in
                                                                  FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu___24
                                                                else
                                                                  act1.FStar_Syntax_Syntax.action_typ
                                                            | uu___23 ->
                                                                act1.FStar_Syntax_Syntax.action_typ in
                                                          let uu___22 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 act_typ in
                                                          (match uu___22 with
                                                           | (act_typ1,
                                                              uu___23, g_t)
                                                               ->
                                                               let env' =
                                                                 let uu___24
                                                                   =
                                                                   FStar_TypeChecker_Env.set_expected_typ
                                                                    env1
                                                                    act_typ1 in
                                                                 {
                                                                   FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.solver);
                                                                   FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.range);
                                                                   FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.curmodule);
                                                                   FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.gamma);
                                                                   FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.gamma_sig);
                                                                   FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.gamma_cache);
                                                                   FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.modules);
                                                                   FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.expected_typ);
                                                                   FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.sigtab);
                                                                   FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.attrtab);
                                                                   FStar_TypeChecker_Env.instantiate_imp
                                                                    = false;
                                                                   FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.effects);
                                                                   FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.generalize);
                                                                   FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.letrecs);
                                                                   FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.top_level);
                                                                   FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.check_uvars);
                                                                   FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.use_eq_strict);
                                                                   FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.is_iface);
                                                                   FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.admit);
                                                                   FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.lax);
                                                                   FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.lax_universes);
                                                                   FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.phase1);
                                                                   FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.failhard);
                                                                   FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.nosynth);
                                                                   FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.uvar_subtyping);
                                                                   FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.tc_term);
                                                                   FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                                                   FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.universe_of);
                                                                   FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                                                   FStar_TypeChecker_Env.teq_nosmt_force
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.teq_nosmt_force);
                                                                   FStar_TypeChecker_Env.subtype_nosmt_force
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.subtype_nosmt_force);
                                                                   FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.use_bv_sorts);
                                                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                   FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.normalized_eff_names);
                                                                   FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.fv_delta_depths);
                                                                   FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.proof_ns);
                                                                   FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.synth_hook);
                                                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                   FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.splice);
                                                                   FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.mpreprocess);
                                                                   FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.postprocess);
                                                                   FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.identifier_info);
                                                                   FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.tc_hooks);
                                                                   FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.dsenv);
                                                                   FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.nbe);
                                                                   FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.strict_args_tab);
                                                                   FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.erasable_types_tab);
                                                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.enable_defer_to_tac);
                                                                   FStar_TypeChecker_Env.unif_allow_ref_guards
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                                                   FStar_TypeChecker_Env.erase_erasable_args
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.erase_erasable_args);
                                                                   FStar_TypeChecker_Env.core_check
                                                                    =
                                                                    (uu___24.FStar_TypeChecker_Env.core_check)
                                                                 } in
                                                               ((let uu___25
                                                                   =
                                                                   FStar_TypeChecker_Env.debug
                                                                    env1
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                 if uu___25
                                                                 then
                                                                   let uu___26
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    act1.FStar_Syntax_Syntax.action_name in
                                                                   let uu___27
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act1.FStar_Syntax_Syntax.action_defn in
                                                                   let uu___28
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ1 in
                                                                   FStar_Compiler_Util.print3
                                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                                    uu___26
                                                                    uu___27
                                                                    uu___28
                                                                 else ());
                                                                (let uu___25
                                                                   =
                                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env'
                                                                    act1.FStar_Syntax_Syntax.action_defn in
                                                                 match uu___25
                                                                 with
                                                                 | (act_defn,
                                                                    uu___26,
                                                                    g_a) ->
                                                                    let act_defn1
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [
                                                                    FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant]
                                                                    env1
                                                                    act_defn in
                                                                    let act_typ2
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [
                                                                    FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant;
                                                                    FStar_TypeChecker_Env.Eager_unfolding;
                                                                    FStar_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ1 in
                                                                    let uu___27
                                                                    =
                                                                    let act_typ3
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    act_typ2 in
                                                                    match 
                                                                    act_typ3.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu___28
                                                                    with
                                                                    | 
                                                                    (bs2,
                                                                    uu___29)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu___30
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu___30 in
                                                                    let uu___30
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k in
                                                                    (match uu___30
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu___31,
                                                                    g) ->
                                                                    (k1, g)))
                                                                    | 
                                                                    uu___28
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                    let uu___32
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                    FStar_Compiler_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu___31
                                                                    uu___32 in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu___30) in
                                                                    FStar_Errors.raise_error
                                                                    uu___29
                                                                    act_defn1.FStar_Syntax_Syntax.pos in
                                                                    (match uu___27
                                                                    with
                                                                    | 
                                                                    (expected_k,
                                                                    g_k) ->
                                                                    let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k in
                                                                    ((
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu___31 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu___30 in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu___29);
                                                                    (let act_typ3
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu___30.FStar_Syntax_Syntax.n in
                                                                    match uu___29
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu___30
                                                                    with
                                                                    | 
                                                                    (bs2, c1)
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu___31
                                                                    with
                                                                    | 
                                                                    (a, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a in
                                                                    [uu___33] in
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu___34] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    = uu___32;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    = uu___33;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu___32
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu___32))
                                                                    | 
                                                                    uu___30
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                    let uu___29
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Generalize.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu___31
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu___31)) in
                                                                    match uu___29
                                                                    with
                                                                    | 
                                                                    (univs,
                                                                    act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ3 in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs
                                                                    act_typ4 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (act1.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (act1.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (act1.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    }))))))) in
                                                   FStar_Compiler_Effect.op_Bar_Greater
                                                     ed2.FStar_Syntax_Syntax.actions
                                                     (FStar_Compiler_List.map
                                                        check_action) in
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
                                               FStar_Syntax_Subst.close_tscheme
                                                 ed_bs ts in
                                             let ed_univs_closing =
                                               FStar_Syntax_Subst.univ_var_closing
                                                 ed_univs in
                                             let uu___15 =
                                               FStar_Syntax_Subst.shift_subst
                                                 (FStar_Compiler_List.length
                                                    ed_bs) ed_univs_closing in
                                             FStar_Syntax_Subst.subst_tscheme
                                               uu___15 ts1 in
                                           let combinators =
                                             {
                                               FStar_Syntax_Syntax.ret_wp =
                                                 ret_wp;
                                               FStar_Syntax_Syntax.bind_wp =
                                                 bind_wp;
                                               FStar_Syntax_Syntax.stronger =
                                                 stronger;
                                               FStar_Syntax_Syntax.if_then_else
                                                 = if_then_else;
                                               FStar_Syntax_Syntax.ite_wp =
                                                 ite_wp;
                                               FStar_Syntax_Syntax.close_wp =
                                                 close_wp;
                                               FStar_Syntax_Syntax.trivial =
                                                 trivial;
                                               FStar_Syntax_Syntax.repr =
                                                 repr;
                                               FStar_Syntax_Syntax.return_repr
                                                 = return_repr;
                                               FStar_Syntax_Syntax.bind_repr
                                                 = bind_repr
                                             } in
                                           let combinators1 =
                                             FStar_Syntax_Util.apply_wp_eff_combinators
                                               cl combinators in
                                           let combinators2 =
                                             match ed2.FStar_Syntax_Syntax.combinators
                                             with
                                             | FStar_Syntax_Syntax.Primitive_eff
                                                 uu___15 ->
                                                 FStar_Syntax_Syntax.Primitive_eff
                                                   combinators1
                                             | FStar_Syntax_Syntax.DM4F_eff
                                                 uu___15 ->
                                                 FStar_Syntax_Syntax.DM4F_eff
                                                   combinators1
                                             | uu___15 ->
                                                 failwith
                                                   "Impossible! tc_eff_decl on a layered effect is not expected" in
                                           let ed3 =
                                             let uu___15 = cl signature in
                                             let uu___16 =
                                               FStar_Compiler_List.map
                                                 (fun a ->
                                                    let uu___17 =
                                                      let uu___18 =
                                                        cl
                                                          ((a.FStar_Syntax_Syntax.action_univs),
                                                            (a.FStar_Syntax_Syntax.action_defn)) in
                                                      FStar_Compiler_Effect.op_Bar_Greater
                                                        uu___18
                                                        FStar_Pervasives_Native.snd in
                                                    let uu___18 =
                                                      let uu___19 =
                                                        cl
                                                          ((a.FStar_Syntax_Syntax.action_univs),
                                                            (a.FStar_Syntax_Syntax.action_typ)) in
                                                      FStar_Compiler_Effect.op_Bar_Greater
                                                        uu___19
                                                        FStar_Pervasives_Native.snd in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (a.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (a.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        =
                                                        (a.FStar_Syntax_Syntax.action_univs);
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (a.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = uu___17;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = uu___18
                                                    }) actions in
                                             {
                                               FStar_Syntax_Syntax.mname =
                                                 (ed2.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.cattributes
                                                 =
                                                 (ed2.FStar_Syntax_Syntax.cattributes);
                                               FStar_Syntax_Syntax.univs =
                                                 (ed2.FStar_Syntax_Syntax.univs);
                                               FStar_Syntax_Syntax.binders =
                                                 (ed2.FStar_Syntax_Syntax.binders);
                                               FStar_Syntax_Syntax.signature
                                                 = uu___15;
                                               FStar_Syntax_Syntax.combinators
                                                 = combinators2;
                                               FStar_Syntax_Syntax.actions =
                                                 uu___16;
                                               FStar_Syntax_Syntax.eff_attrs
                                                 =
                                                 (ed2.FStar_Syntax_Syntax.eff_attrs)
                                             } in
                                           ((let uu___16 =
                                               FStar_Compiler_Effect.op_Less_Bar
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other "ED") in
                                             if uu___16
                                             then
                                               let uu___17 =
                                                 FStar_Syntax_Print.eff_decl_to_string
                                                   false ed3 in
                                               FStar_Compiler_Util.print1
                                                 "Typechecked effect declaration:\n\t%s\n"
                                                 uu___17
                                             else ());
                                            ed3))))))))))))))
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun env ->
    fun ed ->
      fun quals ->
        fun attrs ->
          let uu___ =
            FStar_Compiler_Effect.op_Bar_Greater ed
              FStar_Syntax_Util.is_layered in
          if uu___
          then tc_layered_eff_decl env ed quals attrs
          else
            (let uu___2 = tc_non_layered_eff_decl env ed quals attrs in
             (uu___2, []))
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax))
  =
  fun env ->
    fun m ->
      fun s ->
        let fail uu___ =
          let uu___1 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu___2 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu___1 uu___2 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | { FStar_Syntax_Syntax.binder_bv = a;
                 FStar_Syntax_Syntax.binder_qual = uu___;
                 FStar_Syntax_Syntax.binder_attrs = uu___1;_}::{
                                                                 FStar_Syntax_Syntax.binder_bv
                                                                   = wp;
                                                                 FStar_Syntax_Syntax.binder_qual
                                                                   = uu___2;
                                                                 FStar_Syntax_Syntax.binder_attrs
                                                                   = uu___3;_}::[]
                 -> (a, (wp.FStar_Syntax_Syntax.sort))
             | uu___ -> fail ())
        | uu___ -> fail ()
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0 ->
    fun sub ->
      (let uu___1 =
         FStar_Compiler_Effect.op_Less_Bar (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc") in
       if uu___1
       then
         let uu___2 = FStar_Syntax_Print.sub_eff_to_string sub in
         FStar_Compiler_Util.print1 "Typechecking sub_effect: %s\n" uu___2
       else ());
      (let lift_ts =
         FStar_Compiler_Effect.op_Bar_Greater sub.FStar_Syntax_Syntax.lift
           FStar_Compiler_Util.must in
       let r =
         let uu___1 =
           FStar_Compiler_Effect.op_Bar_Greater lift_ts
             FStar_Pervasives_Native.snd in
         uu___1.FStar_Syntax_Syntax.pos in
       let uu___1 = check_and_gen env0 "" "lift" Prims.int_one lift_ts in
       match uu___1 with
       | (us, lift, lift_ty) ->
           ((let uu___3 =
               FStar_Compiler_Effect.op_Less_Bar
                 (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu___3
             then
               let uu___4 = FStar_Syntax_Print.tscheme_to_string (us, lift) in
               let uu___5 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift_ty) in
               FStar_Compiler_Util.print2
                 "Typechecked lift: %s and lift_ty: %s\n" uu___4 uu___5
             else ());
            (let uu___3 = FStar_Syntax_Subst.open_univ_vars us lift_ty in
             match uu___3 with
             | (us1, lift_ty1) ->
                 let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                 let lift_t_shape_error s =
                   let uu___5 =
                     FStar_Ident.string_of_lid sub.FStar_Syntax_Syntax.source in
                   let uu___6 =
                     FStar_Ident.string_of_lid sub.FStar_Syntax_Syntax.target in
                   let uu___7 = FStar_Syntax_Print.term_to_string lift_ty1 in
                   FStar_Compiler_Util.format4
                     "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                     uu___5 uu___6 s uu___7 in
                 let uu___5 =
                   let uu___6 =
                     let uu___7 = FStar_Syntax_Util.type_u () in
                     FStar_Compiler_Effect.op_Bar_Greater uu___7
                       (fun uu___8 ->
                          match uu___8 with
                          | (t, u) ->
                              let uu___9 =
                                let uu___10 =
                                  FStar_Syntax_Syntax.gen_bv "a"
                                    FStar_Pervasives_Native.None t in
                                FStar_Compiler_Effect.op_Bar_Greater uu___10
                                  FStar_Syntax_Syntax.mk_binder in
                              (uu___9, u)) in
                   match uu___6 with
                   | (a, u_a) ->
                       let uu___7 =
                         let uu___8 =
                           let uu___9 = FStar_Syntax_Subst.compress lift_ty1 in
                           uu___9.FStar_Syntax_Syntax.n in
                         match uu___8 with
                         | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                             (FStar_Compiler_List.length bs) >=
                               (Prims.of_int (2))
                             ->
                             let uu___9 = FStar_Syntax_Subst.open_binders bs in
                             (match uu___9 with
                              | { FStar_Syntax_Syntax.binder_bv = a';
                                  FStar_Syntax_Syntax.binder_qual = uu___10;
                                  FStar_Syntax_Syntax.binder_attrs = uu___11;_}::bs1
                                  ->
                                  let uu___12 =
                                    let uu___13 =
                                      let uu___14 =
                                        FStar_Compiler_Effect.op_Bar_Greater
                                          bs1
                                          (FStar_Compiler_List.splitAt
                                             ((FStar_Compiler_List.length bs1)
                                                - Prims.int_one)) in
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        uu___14 FStar_Pervasives_Native.fst in
                                    let uu___14 =
                                      let uu___15 =
                                        let uu___16 =
                                          let uu___17 =
                                            let uu___18 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a.FStar_Syntax_Syntax.binder_bv in
                                            (a', uu___18) in
                                          FStar_Syntax_Syntax.NT uu___17 in
                                        [uu___16] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu___15 in
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      uu___13 uu___14 in
                                  let uu___13 =
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      (FStar_Syntax_Util.comp_effect_name c)
                                      (FStar_TypeChecker_Env.norm_eff_name
                                         env) in
                                  (uu___12, uu___13))
                         | uu___9 ->
                             let uu___10 =
                               let uu___11 =
                                 lift_t_shape_error
                                   "either not an arrow, or not enough binders" in
                               (FStar_Errors.Fatal_UnexpectedExpressionType,
                                 uu___11) in
                             FStar_Errors.raise_error uu___10 r in
                       (match uu___7 with
                        | (rest_bs, lift_eff) ->
                            ((let uu___9 =
                                let uu___10 =
                                  (FStar_Ident.lid_equals lift_eff
                                     FStar_Parser_Const.effect_PURE_lid)
                                    ||
                                    ((FStar_Ident.lid_equals lift_eff
                                        FStar_Parser_Const.effect_GHOST_lid)
                                       &&
                                       (FStar_TypeChecker_Env.is_erasable_effect
                                          env sub.FStar_Syntax_Syntax.source)) in
                                Prims.op_Negation uu___10 in
                              if uu___9
                              then
                                let uu___10 =
                                  let uu___11 =
                                    lift_t_shape_error
                                      "the lift combinator has an unexpected effect: it must either be PURE or if the source effect is erasable then may be GHOST" in
                                  (FStar_Errors.Fatal_UnexpectedExpressionType,
                                    uu___11) in
                                FStar_Errors.raise_error uu___10 r
                              else ());
                             (let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    FStar_TypeChecker_Env.push_binders env (a
                                      :: rest_bs) in
                                  let uu___12 =
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      a.FStar_Syntax_Syntax.binder_bv
                                      FStar_Syntax_Syntax.bv_to_name in
                                  FStar_TypeChecker_Util.fresh_effect_repr_en
                                    uu___11 r sub.FStar_Syntax_Syntax.source
                                    u_a uu___12 in
                                match uu___10 with
                                | (f_sort, g) ->
                                    let uu___11 =
                                      let uu___12 =
                                        FStar_Syntax_Syntax.gen_bv "f"
                                          FStar_Pervasives_Native.None f_sort in
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        uu___12 FStar_Syntax_Syntax.mk_binder in
                                    (uu___11, g) in
                              match uu___9 with
                              | (f_b, g_f_b) ->
                                  let bs = a :: rest_bs in
                                  let uu___10 =
                                    let uu___11 =
                                      FStar_TypeChecker_Env.push_binders env
                                        bs in
                                    let uu___12 =
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        a.FStar_Syntax_Syntax.binder_bv
                                        FStar_Syntax_Syntax.bv_to_name in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu___11 r
                                      sub.FStar_Syntax_Syntax.target u_a
                                      uu___12 in
                                  (match uu___10 with
                                   | (repr, g_repr) ->
                                       let uu___11 =
                                         let uu___12 =
                                           FStar_TypeChecker_Env.push_binders
                                             env bs in
                                         let uu___13 =
                                           let uu___14 =
                                             FStar_Ident.string_of_lid
                                               sub.FStar_Syntax_Syntax.source in
                                           let uu___15 =
                                             FStar_Ident.string_of_lid
                                               sub.FStar_Syntax_Syntax.target in
                                           FStar_Compiler_Util.format2
                                             "implicit for pure_wp in typechecking lift %s~>%s"
                                             uu___14 uu___15 in
                                         pure_wp_uvar uu___12 repr uu___13 r in
                                       (match uu___11 with
                                        | (pure_wp_uvar1, guard_wp) ->
                                            let c =
                                              let uu___12 =
                                                let uu___13 =
                                                  let uu___14 =
                                                    FStar_TypeChecker_Env.new_u_univ
                                                      () in
                                                  [uu___14] in
                                                let uu___14 =
                                                  let uu___15 =
                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                      pure_wp_uvar1
                                                      FStar_Syntax_Syntax.as_arg in
                                                  [uu___15] in
                                                {
                                                  FStar_Syntax_Syntax.comp_univs
                                                    = uu___13;
                                                  FStar_Syntax_Syntax.effect_name
                                                    = lift_eff;
                                                  FStar_Syntax_Syntax.result_typ
                                                    = repr;
                                                  FStar_Syntax_Syntax.effect_args
                                                    = uu___14;
                                                  FStar_Syntax_Syntax.flags =
                                                    []
                                                } in
                                              FStar_Syntax_Syntax.mk_Comp
                                                uu___12 in
                                            let uu___12 =
                                              FStar_Syntax_Util.arrow
                                                (FStar_Compiler_List.op_At bs
                                                   [f_b]) c in
                                            let uu___13 =
                                              let uu___14 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_f_b g_repr in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu___14 guard_wp in
                                            (uu___12, uu___13)))))) in
                 (match uu___5 with
                  | (k, g_k) ->
                      ((let uu___7 =
                          FStar_Compiler_Effect.op_Less_Bar
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "LayeredEffectsTc") in
                        if uu___7
                        then
                          let uu___8 = FStar_Syntax_Print.term_to_string k in
                          FStar_Compiler_Util.print1
                            "tc_layered_lift: before unification k: %s\n"
                            uu___8
                        else ());
                       (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k in
                        FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                        FStar_TypeChecker_Rel.force_trivial_guard env g;
                        (let uu___10 =
                           FStar_Compiler_Effect.op_Less_Bar
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "LayeredEffectsTc") in
                         if uu___10
                         then
                           let uu___11 = FStar_Syntax_Print.term_to_string k in
                           FStar_Compiler_Util.print1
                             "After unification k: %s\n" uu___11
                         else ());
                        (let k1 =
                           FStar_Compiler_Effect.op_Bar_Greater k
                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                env) in
                         let check_non_informative_binders =
                           (FStar_TypeChecker_Env.is_reifiable_effect env
                              sub.FStar_Syntax_Syntax.target)
                             &&
                             (let uu___10 =
                                FStar_TypeChecker_Env.fv_with_lid_has_attr
                                  env sub.FStar_Syntax_Syntax.target
                                  FStar_Parser_Const.allow_informative_binders_attr in
                              Prims.op_Negation uu___10) in
                         (let uu___10 =
                            let uu___11 = FStar_Syntax_Subst.compress k1 in
                            uu___11.FStar_Syntax_Syntax.n in
                          match uu___10 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                              let uu___11 = FStar_Syntax_Subst.open_comp bs c in
                              (match uu___11 with
                               | (a::bs1, c1) ->
                                   let res_t =
                                     FStar_Syntax_Util.comp_result c1 in
                                   let uu___12 =
                                     let uu___13 =
                                       FStar_Compiler_List.splitAt
                                         ((FStar_Compiler_List.length bs1) -
                                            Prims.int_one) bs1 in
                                     FStar_Compiler_Effect.op_Bar_Greater
                                       uu___13
                                       (fun uu___14 ->
                                          match uu___14 with
                                          | (l1, l2) ->
                                              let uu___15 =
                                                FStar_Compiler_List.hd l2 in
                                              (l1, uu___15)) in
                                   (match uu___12 with
                                    | (bs2, f_b) ->
                                        let env1 =
                                          FStar_TypeChecker_Env.push_binders
                                            env [a] in
                                        validate_layered_effect_binders env1
                                          bs2 check_non_informative_binders r)));
                         (let sub1 =
                            let uu___10 =
                              let uu___11 =
                                let uu___12 =
                                  FStar_Compiler_Effect.op_Bar_Greater k1
                                    (FStar_Syntax_Subst.close_univ_vars us1) in
                                (us1, uu___12) in
                              FStar_Pervasives_Native.Some uu___11 in
                            {
                              FStar_Syntax_Syntax.source =
                                (sub.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (sub.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = uu___10;
                              FStar_Syntax_Syntax.lift =
                                (FStar_Pervasives_Native.Some (us1, lift))
                            } in
                          (let uu___11 =
                             FStar_Compiler_Effect.op_Less_Bar
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffectsTc") in
                           if uu___11
                           then
                             let uu___12 =
                               FStar_Syntax_Print.sub_eff_to_string sub1 in
                             FStar_Compiler_Util.print1
                               "Final sub_effect: %s\n" uu___12
                           else ());
                          sub1))))))))
let (check_lift_for_erasable_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Compiler_Range.range -> unit)
  =
  fun env ->
    fun m1 ->
      fun m2 ->
        fun r ->
          let err reason =
            let uu___ =
              let uu___1 =
                let uu___2 = FStar_Ident.string_of_lid m1 in
                let uu___3 = FStar_Ident.string_of_lid m2 in
                FStar_Compiler_Util.format3
                  "Error defining a lift/subcomp %s ~> %s: %s" uu___2 uu___3
                  reason in
              (FStar_Errors.Fatal_UnexpectedEffect, uu___1) in
            FStar_Errors.raise_error uu___ r in
          let m11 = FStar_TypeChecker_Env.norm_eff_name env m1 in
          let uu___ =
            FStar_Ident.lid_equals m11 FStar_Parser_Const.effect_GHOST_lid in
          if uu___
          then err "user-defined lifts from GHOST effect are not allowed"
          else
            (let m1_erasable =
               FStar_TypeChecker_Env.is_erasable_effect env m11 in
             let m2_erasable =
               FStar_TypeChecker_Env.is_erasable_effect env m2 in
             let uu___2 =
               (m2_erasable && (Prims.op_Negation m1_erasable)) &&
                 (let uu___3 =
                    FStar_Ident.lid_equals m11
                      FStar_Parser_Const.effect_PURE_lid in
                  Prims.op_Negation uu___3) in
             if uu___2
             then
               err
                 "cannot lift a non-erasable effect to an erasable effect unless the non-erasable effect is PURE"
             else ())
let (tc_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Compiler_Range.range -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env ->
    fun sub ->
      fun r ->
        (let uu___1 =
           FStar_Ident.lid_equals sub.FStar_Syntax_Syntax.source
             sub.FStar_Syntax_Syntax.target in
         if uu___1
         then
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 FStar_Ident.string_of_lid sub.FStar_Syntax_Syntax.source in
               FStar_Compiler_Util.format1
                 "Cannot define a lift with same source and target (%s)"
                 uu___4 in
             (FStar_Errors.Fatal_UnexpectedEffect, uu___3) in
           FStar_Errors.raise_error uu___2 r
         else ());
        (let check_and_gen1 env1 t k =
           let uu___1 =
             FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k in
           FStar_TypeChecker_Generalize.generalize_universes env1 uu___1 in
         check_lift_for_erasable_effects env sub.FStar_Syntax_Syntax.source
           sub.FStar_Syntax_Syntax.target r;
         (let ed_src =
            FStar_TypeChecker_Env.get_effect_decl env
              sub.FStar_Syntax_Syntax.source in
          let ed_tgt =
            FStar_TypeChecker_Env.get_effect_decl env
              sub.FStar_Syntax_Syntax.target in
          let uu___2 =
            (FStar_Compiler_Effect.op_Bar_Greater ed_src
               FStar_Syntax_Util.is_layered)
              ||
              (FStar_Compiler_Effect.op_Bar_Greater ed_tgt
                 FStar_Syntax_Util.is_layered) in
          if uu___2
          then
            let uu___3 = FStar_TypeChecker_Env.set_range env r in
            tc_layered_lift uu___3 sub
          else
            (let uu___4 =
               let uu___5 =
                 FStar_TypeChecker_Env.lookup_effect_lid env
                   sub.FStar_Syntax_Syntax.source in
               monad_signature env sub.FStar_Syntax_Syntax.source uu___5 in
             match uu___4 with
             | (a, wp_a_src) ->
                 let uu___5 =
                   let uu___6 =
                     FStar_TypeChecker_Env.lookup_effect_lid env
                       sub.FStar_Syntax_Syntax.target in
                   monad_signature env sub.FStar_Syntax_Syntax.target uu___6 in
                 (match uu___5 with
                  | (b, wp_b_tgt) ->
                      let wp_a_tgt =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 = FStar_Syntax_Syntax.bv_to_name a in
                              (b, uu___9) in
                            FStar_Syntax_Syntax.NT uu___8 in
                          [uu___7] in
                        FStar_Syntax_Subst.subst uu___6 wp_b_tgt in
                      let expected_k =
                        let uu___6 =
                          let uu___7 = FStar_Syntax_Syntax.mk_binder a in
                          let uu___8 =
                            let uu___9 =
                              FStar_Syntax_Syntax.null_binder wp_a_src in
                            [uu___9] in
                          uu___7 :: uu___8 in
                        let uu___7 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                        FStar_Syntax_Util.arrow uu___6 uu___7 in
                      let repr_type eff_name a1 wp =
                        (let uu___7 =
                           let uu___8 =
                             FStar_TypeChecker_Env.is_reifiable_effect env
                               eff_name in
                           Prims.op_Negation uu___8 in
                         if uu___7
                         then
                           let uu___8 =
                             let uu___9 =
                               let uu___10 =
                                 FStar_Ident.string_of_lid eff_name in
                               FStar_Compiler_Util.format1
                                 "Effect %s cannot be reified" uu___10 in
                             (FStar_Errors.Fatal_EffectCannotBeReified,
                               uu___9) in
                           let uu___9 = FStar_TypeChecker_Env.get_range env in
                           FStar_Errors.raise_error uu___8 uu___9
                         else ());
                        (let uu___7 =
                           FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                         match uu___7 with
                         | FStar_Pervasives_Native.None ->
                             failwith
                               "internal error: reifiable effect has no decl?"
                         | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                             let repr =
                               let uu___8 =
                                 let uu___9 =
                                   FStar_Compiler_Effect.op_Bar_Greater ed
                                     FStar_Syntax_Util.get_eff_repr in
                                 FStar_Compiler_Effect.op_Bar_Greater uu___9
                                   FStar_Compiler_Util.must in
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [FStar_Syntax_Syntax.U_unknown] env ed
                                 uu___8 in
                             let uu___8 =
                               let uu___9 =
                                 let uu___10 =
                                   let uu___11 =
                                     FStar_Syntax_Syntax.as_arg a1 in
                                   let uu___12 =
                                     let uu___13 =
                                       FStar_Syntax_Syntax.as_arg wp in
                                     [uu___13] in
                                   uu___11 :: uu___12 in
                                 (repr, uu___10) in
                               FStar_Syntax_Syntax.Tm_app uu___9 in
                             let uu___9 = FStar_TypeChecker_Env.get_range env in
                             FStar_Syntax_Syntax.mk uu___8 uu___9) in
                      let uu___6 =
                        match ((sub.FStar_Syntax_Syntax.lift),
                                (sub.FStar_Syntax_Syntax.lift_wp))
                        with
                        | (FStar_Pervasives_Native.None,
                           FStar_Pervasives_Native.None) ->
                            failwith "Impossible (parser)"
                        | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                            ->
                            let uu___7 =
                              if
                                (FStar_Compiler_List.length uvs) >
                                  Prims.int_zero
                              then
                                let uu___8 =
                                  FStar_Syntax_Subst.univ_var_opening uvs in
                                match uu___8 with
                                | (usubst, uvs1) ->
                                    let uu___9 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs1 in
                                    let uu___10 =
                                      FStar_Syntax_Subst.subst usubst lift_wp in
                                    (uu___9, uu___10)
                              else (env, lift_wp) in
                            (match uu___7 with
                             | (env1, lift_wp1) ->
                                 let lift_wp2 =
                                   if
                                     (FStar_Compiler_List.length uvs) =
                                       Prims.int_zero
                                   then
                                     check_and_gen1 env1 lift_wp1 expected_k
                                   else
                                     (let lift_wp3 =
                                        FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                          env1 lift_wp1 expected_k in
                                      let uu___9 =
                                        FStar_Syntax_Subst.close_univ_vars
                                          uvs lift_wp3 in
                                      (uvs, uu___9)) in
                                 (lift, lift_wp2))
                        | (FStar_Pervasives_Native.Some (what, lift),
                           FStar_Pervasives_Native.None) ->
                            let uu___7 =
                              if
                                (FStar_Compiler_List.length what) >
                                  Prims.int_zero
                              then
                                let uu___8 =
                                  FStar_Syntax_Subst.univ_var_opening what in
                                match uu___8 with
                                | (usubst, uvs) ->
                                    let uu___9 =
                                      FStar_Syntax_Subst.subst usubst lift in
                                    (uvs, uu___9)
                              else ([], lift) in
                            (match uu___7 with
                             | (uvs, lift1) ->
                                 ((let uu___9 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "ED") in
                                   if uu___9
                                   then
                                     let uu___10 =
                                       FStar_Syntax_Print.term_to_string
                                         lift1 in
                                     FStar_Compiler_Util.print1
                                       "Lift for free : %s\n" uu___10
                                   else ());
                                  (let dmff_env =
                                     FStar_TypeChecker_DMFF.empty env
                                       (FStar_TypeChecker_TcTerm.tc_constant
                                          env FStar_Compiler_Range.dummyRange) in
                                   let uu___9 =
                                     let uu___10 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env uvs in
                                     FStar_TypeChecker_TcTerm.tc_term uu___10
                                       lift1 in
                                   match uu___9 with
                                   | (lift2, comp, uu___10) ->
                                       let uu___11 =
                                         FStar_TypeChecker_DMFF.star_expr
                                           dmff_env lift2 in
                                       (match uu___11 with
                                        | (uu___12, lift_wp, lift_elab) ->
                                            let lift_wp1 =
                                              FStar_TypeChecker_DMFF.recheck_debug
                                                "lift-wp" env lift_wp in
                                            let lift_elab1 =
                                              FStar_TypeChecker_DMFF.recheck_debug
                                                "lift-elab" env lift_elab in
                                            if
                                              (FStar_Compiler_List.length uvs)
                                                = Prims.int_zero
                                            then
                                              let uu___13 =
                                                let uu___14 =
                                                  FStar_TypeChecker_Generalize.generalize_universes
                                                    env lift_elab1 in
                                                FStar_Pervasives_Native.Some
                                                  uu___14 in
                                              let uu___14 =
                                                FStar_TypeChecker_Generalize.generalize_universes
                                                  env lift_wp1 in
                                              (uu___13, uu___14)
                                            else
                                              (let uu___14 =
                                                 let uu___15 =
                                                   let uu___16 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift_elab1 in
                                                   (uvs, uu___16) in
                                                 FStar_Pervasives_Native.Some
                                                   uu___15 in
                                               let uu___15 =
                                                 let uu___16 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_wp1 in
                                                 (uvs, uu___16) in
                                               (uu___14, uu___15)))))) in
                      (match uu___6 with
                       | (lift, lift_wp) ->
                           let env1 =
                             {
                               FStar_TypeChecker_Env.solver =
                                 (env.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (env.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (env.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (env.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (env.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (env.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (env.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (env.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (env.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (env.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (env.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (env.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (env.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (env.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (env.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (env.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq_strict =
                                 (env.FStar_TypeChecker_Env.use_eq_strict);
                               FStar_TypeChecker_Env.is_iface =
                                 (env.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (env.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (env.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (env.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (env.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (env.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (env.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (env.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                 =
                                 (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                               FStar_TypeChecker_Env.universe_of =
                                 (env.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                 =
                                 (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                               FStar_TypeChecker_Env.teq_nosmt_force =
                                 (env.FStar_TypeChecker_Env.teq_nosmt_force);
                               FStar_TypeChecker_Env.subtype_nosmt_force =
                                 (env.FStar_TypeChecker_Env.subtype_nosmt_force);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (env.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (env.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (env.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (env.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (env.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (env.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
                               FStar_TypeChecker_Env.splice =
                                 (env.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.mpreprocess =
                                 (env.FStar_TypeChecker_Env.mpreprocess);
                               FStar_TypeChecker_Env.postprocess =
                                 (env.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.identifier_info =
                                 (env.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (env.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (env.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (env.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (env.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (env.FStar_TypeChecker_Env.erasable_types_tab);
                               FStar_TypeChecker_Env.enable_defer_to_tac =
                                 (env.FStar_TypeChecker_Env.enable_defer_to_tac);
                               FStar_TypeChecker_Env.unif_allow_ref_guards =
                                 (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
                               FStar_TypeChecker_Env.erase_erasable_args =
                                 (env.FStar_TypeChecker_Env.erase_erasable_args);
                               FStar_TypeChecker_Env.core_check =
                                 (env.FStar_TypeChecker_Env.core_check)
                             } in
                           let lift1 =
                             match lift with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some (uvs, lift2) ->
                                 let uu___7 =
                                   let uu___8 =
                                     FStar_Syntax_Subst.univ_var_opening uvs in
                                   match uu___8 with
                                   | (usubst, uvs1) ->
                                       let uu___9 =
                                         FStar_TypeChecker_Env.push_univ_vars
                                           env1 uvs1 in
                                       let uu___10 =
                                         FStar_Syntax_Subst.subst usubst
                                           lift2 in
                                       (uu___9, uu___10) in
                                 (match uu___7 with
                                  | (env2, lift3) ->
                                      let uu___8 =
                                        let uu___9 =
                                          FStar_TypeChecker_Env.lookup_effect_lid
                                            env2
                                            sub.FStar_Syntax_Syntax.source in
                                        monad_signature env2
                                          sub.FStar_Syntax_Syntax.source
                                          uu___9 in
                                      (match uu___8 with
                                       | (a1, wp_a_src1) ->
                                           let wp_a =
                                             FStar_Syntax_Syntax.new_bv
                                               FStar_Pervasives_Native.None
                                               wp_a_src1 in
                                           let a_typ =
                                             FStar_Syntax_Syntax.bv_to_name
                                               a1 in
                                           let wp_a_typ =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_a in
                                           let repr_f =
                                             repr_type
                                               sub.FStar_Syntax_Syntax.source
                                               a_typ wp_a_typ in
                                           let repr_result =
                                             let lift_wp1 =
                                               FStar_TypeChecker_Normalize.normalize
                                                 [FStar_TypeChecker_Env.EraseUniverses;
                                                 FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                 env2
                                                 (FStar_Pervasives_Native.snd
                                                    lift_wp) in
                                             let lift_wp_a =
                                               let uu___9 =
                                                 let uu___10 =
                                                   let uu___11 =
                                                     let uu___12 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ in
                                                     let uu___13 =
                                                       let uu___14 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ in
                                                       [uu___14] in
                                                     uu___12 :: uu___13 in
                                                   (lift_wp1, uu___11) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu___10 in
                                               let uu___10 =
                                                 FStar_TypeChecker_Env.get_range
                                                   env2 in
                                               FStar_Syntax_Syntax.mk uu___9
                                                 uu___10 in
                                             repr_type
                                               sub.FStar_Syntax_Syntax.target
                                               a_typ lift_wp_a in
                                           let expected_k1 =
                                             let uu___9 =
                                               let uu___10 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a1 in
                                               let uu___11 =
                                                 let uu___12 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     wp_a in
                                                 let uu___13 =
                                                   let uu___14 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       repr_f in
                                                   [uu___14] in
                                                 uu___12 :: uu___13 in
                                               uu___10 :: uu___11 in
                                             let uu___10 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 repr_result in
                                             FStar_Syntax_Util.arrow uu___9
                                               uu___10 in
                                           let uu___9 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env2 expected_k1 in
                                           (match uu___9 with
                                            | (expected_k2, uu___10, uu___11)
                                                ->
                                                let lift4 =
                                                  if
                                                    (FStar_Compiler_List.length
                                                       uvs)
                                                      = Prims.int_zero
                                                  then
                                                    check_and_gen1 env2 lift3
                                                      expected_k2
                                                  else
                                                    (let lift5 =
                                                       FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                                         env2 lift3
                                                         expected_k2 in
                                                     let uu___13 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         uvs lift5 in
                                                     (uvs, uu___13)) in
                                                FStar_Pervasives_Native.Some
                                                  lift4))) in
                           ((let uu___8 =
                               let uu___9 =
                                 let uu___10 =
                                   FStar_Compiler_Effect.op_Bar_Greater
                                     lift_wp FStar_Pervasives_Native.fst in
                                 FStar_Compiler_Effect.op_Bar_Greater uu___10
                                   FStar_Compiler_List.length in
                               uu___9 <> Prims.int_one in
                             if uu___8
                             then
                               let uu___9 =
                                 let uu___10 =
                                   let uu___11 =
                                     FStar_Syntax_Print.lid_to_string
                                       sub.FStar_Syntax_Syntax.source in
                                   let uu___12 =
                                     FStar_Syntax_Print.lid_to_string
                                       sub.FStar_Syntax_Syntax.target in
                                   let uu___13 =
                                     let uu___14 =
                                       let uu___15 =
                                         FStar_Compiler_Effect.op_Bar_Greater
                                           lift_wp
                                           FStar_Pervasives_Native.fst in
                                       FStar_Compiler_Effect.op_Bar_Greater
                                         uu___15 FStar_Compiler_List.length in
                                     FStar_Compiler_Effect.op_Bar_Greater
                                       uu___14
                                       FStar_Compiler_Util.string_of_int in
                                   FStar_Compiler_Util.format3
                                     "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                     uu___11 uu___12 uu___13 in
                                 (FStar_Errors.Fatal_TooManyUniverse,
                                   uu___10) in
                               FStar_Errors.raise_error uu___9 r
                             else ());
                            (let uu___9 =
                               (FStar_Compiler_Util.is_some lift1) &&
                                 (let uu___10 =
                                    let uu___11 =
                                      let uu___12 =
                                        FStar_Compiler_Effect.op_Bar_Greater
                                          lift1 FStar_Compiler_Util.must in
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        uu___12 FStar_Pervasives_Native.fst in
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      uu___11 FStar_Compiler_List.length in
                                  uu___10 <> Prims.int_one) in
                             if uu___9
                             then
                               let uu___10 =
                                 let uu___11 =
                                   let uu___12 =
                                     FStar_Syntax_Print.lid_to_string
                                       sub.FStar_Syntax_Syntax.source in
                                   let uu___13 =
                                     FStar_Syntax_Print.lid_to_string
                                       sub.FStar_Syntax_Syntax.target in
                                   let uu___14 =
                                     let uu___15 =
                                       let uu___16 =
                                         let uu___17 =
                                           FStar_Compiler_Effect.op_Bar_Greater
                                             lift1 FStar_Compiler_Util.must in
                                         FStar_Compiler_Effect.op_Bar_Greater
                                           uu___17
                                           FStar_Pervasives_Native.fst in
                                       FStar_Compiler_Effect.op_Bar_Greater
                                         uu___16 FStar_Compiler_List.length in
                                     FStar_Compiler_Effect.op_Bar_Greater
                                       uu___15
                                       FStar_Compiler_Util.string_of_int in
                                   FStar_Compiler_Util.format3
                                     "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                     uu___12 uu___13 uu___14 in
                                 (FStar_Errors.Fatal_TooManyUniverse,
                                   uu___11) in
                               FStar_Errors.raise_error uu___10 r
                             else ());
                            {
                              FStar_Syntax_Syntax.source =
                                (sub.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (sub.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            }))))))
let (tc_effect_abbrev :
  FStar_TypeChecker_Env.env ->
    (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names *
      FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) ->
      FStar_Compiler_Range.range ->
        (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun env ->
    fun uu___ ->
      fun r ->
        match uu___ with
        | (lid, uvs, tps, c) ->
            let env0 = env in
            let uu___1 =
              if (FStar_Compiler_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu___3 = FStar_Syntax_Subst.univ_var_opening uvs in
                 match uu___3 with
                 | (usubst, uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                     let c1 =
                       let uu___4 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_Compiler_List.length tps1) usubst in
                       FStar_Syntax_Subst.subst_comp uu___4 c in
                     let uu___4 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                     (uu___4, uvs1, tps1, c1)) in
            (match uu___1 with
             | (env1, uvs1, tps1, c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r in
                 let uu___2 = FStar_Syntax_Subst.open_comp tps1 c1 in
                 (match uu___2 with
                  | (tps2, c2) ->
                      let uu___3 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                      (match uu___3 with
                       | (tps3, env3, us) ->
                           let uu___4 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                           (match uu___4 with
                            | (c3, u, g) ->
                                let is_default_effect =
                                  let uu___5 =
                                    let uu___6 =
                                      FStar_Compiler_Effect.op_Bar_Greater c3
                                        FStar_Syntax_Util.comp_effect_name in
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      uu___6
                                      (FStar_TypeChecker_Env.get_default_effect
                                         env3) in
                                  match uu___5 with
                                  | FStar_Pervasives_Native.None -> false
                                  | FStar_Pervasives_Native.Some l ->
                                      FStar_Ident.lid_equals l lid in
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | { FStar_Syntax_Syntax.binder_bv = x;
                                        FStar_Syntax_Syntax.binder_qual =
                                          uu___7;
                                        FStar_Syntax_Syntax.binder_attrs =
                                          uu___8;_}::tl
                                        ->
                                        (if
                                           is_default_effect &&
                                             (Prims.op_Negation (tl = []))
                                         then
                                           (let uu___10 =
                                              let uu___11 =
                                                let uu___12 =
                                                  FStar_Ident.string_of_lid
                                                    lid in
                                                let uu___13 =
                                                  let uu___14 =
                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                      c3
                                                      FStar_Syntax_Util.comp_effect_name in
                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                    uu___14
                                                    FStar_Ident.string_of_lid in
                                                FStar_Compiler_Util.format2
                                                  "Effect %s is marked as a default effect for %s, but it has more than one arguments"
                                                  uu___12 uu___13 in
                                              (FStar_Errors.Fatal_UnexpectedEffect,
                                                uu___11) in
                                            FStar_Errors.raise_error uu___10
                                              r)
                                         else ();
                                         FStar_Syntax_Syntax.bv_to_name x)
                                    | uu___7 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3 in
                                  let uu___7 =
                                    let uu___8 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ in
                                    Prims.op_Negation uu___8 in
                                  if uu___7
                                  then
                                    let uu___8 =
                                      let uu___9 =
                                        let uu___10 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ in
                                        let uu___11 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ in
                                        FStar_Compiler_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu___10 uu___11 in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu___9) in
                                    FStar_Errors.raise_error uu___8 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3 in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3 in
                                  let uu___7 =
                                    let uu___8 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r in
                                    FStar_TypeChecker_Generalize.generalize_universes
                                      env0 uu___8 in
                                  match uu___7 with
                                  | (uvs2, t) ->
                                      let uu___8 =
                                        let uu___9 =
                                          let uu___10 =
                                            let uu___11 =
                                              FStar_Syntax_Subst.compress t in
                                            uu___11.FStar_Syntax_Syntax.n in
                                          (tps4, uu___10) in
                                        match uu___9 with
                                        | ([], FStar_Syntax_Syntax.Tm_arrow
                                           (uu___10, c5)) -> ([], c5)
                                        | (uu___10,
                                           FStar_Syntax_Syntax.Tm_arrow
                                           (tps5, c5)) -> (tps5, c5)
                                        | uu___10 ->
                                            failwith
                                              "Impossible (t is an arrow)" in
                                      (match uu___8 with
                                       | (tps5, c5) ->
                                           (if
                                              (FStar_Compiler_List.length
                                                 uvs2)
                                                <> Prims.int_one
                                            then
                                              (let uu___10 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t in
                                               match uu___10 with
                                               | (uu___11, t1) ->
                                                   let uu___12 =
                                                     let uu___13 =
                                                       let uu___14 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid in
                                                       let uu___15 =
                                                         FStar_Compiler_Effect.op_Bar_Greater
                                                           (FStar_Compiler_List.length
                                                              uvs2)
                                                           FStar_Compiler_Util.string_of_int in
                                                       let uu___16 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1 in
                                                       FStar_Compiler_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu___14 uu___15
                                                         uu___16 in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu___13) in
                                                   FStar_Errors.raise_error
                                                     uu___12 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
let (check_polymonadic_bind_for_erasable_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident -> FStar_Compiler_Range.range -> unit)
  =
  fun env ->
    fun m ->
      fun n ->
        fun p ->
          fun r ->
            let err reason =
              let uu___ =
                let uu___1 =
                  let uu___2 = FStar_Ident.string_of_lid m in
                  let uu___3 = FStar_Ident.string_of_lid n in
                  let uu___4 = FStar_Ident.string_of_lid p in
                  FStar_Compiler_Util.format4
                    "Error definition polymonadic bind (%s, %s) |> %s: %s"
                    uu___2 uu___3 uu___4 reason in
                (FStar_Errors.Fatal_UnexpectedEffect, uu___1) in
              FStar_Errors.raise_error uu___ r in
            let m1 = FStar_TypeChecker_Env.norm_eff_name env m in
            let n1 = FStar_TypeChecker_Env.norm_eff_name env n in
            let uu___ =
              (FStar_Ident.lid_equals m1 FStar_Parser_Const.effect_GHOST_lid)
                ||
                (FStar_Ident.lid_equals n1
                   FStar_Parser_Const.effect_GHOST_lid) in
            if uu___
            then
              err
                "GHOST computations are not allowed to be composed using user-defined polymonadic binds"
            else
              (let m_erasable =
                 FStar_TypeChecker_Env.is_erasable_effect env m1 in
               let n_erasable =
                 FStar_TypeChecker_Env.is_erasable_effect env n1 in
               let p_erasable =
                 FStar_TypeChecker_Env.is_erasable_effect env p in
               if p_erasable
               then
                 let uu___2 =
                   (Prims.op_Negation m_erasable) &&
                     (let uu___3 =
                        FStar_Ident.lid_equals m1
                          FStar_Parser_Const.effect_PURE_lid in
                      Prims.op_Negation uu___3) in
                 (if uu___2
                  then
                    let uu___3 =
                      let uu___4 = FStar_Ident.string_of_lid m1 in
                      FStar_Compiler_Util.format1
                        "target effect is erasable but %s is neither erasable nor PURE"
                        uu___4 in
                    err uu___3
                  else
                    (let uu___4 =
                       (Prims.op_Negation n_erasable) &&
                         (let uu___5 =
                            FStar_Ident.lid_equals n1
                              FStar_Parser_Const.effect_PURE_lid in
                          Prims.op_Negation uu___5) in
                     if uu___4
                     then
                       let uu___5 =
                         let uu___6 = FStar_Ident.string_of_lid n1 in
                         FStar_Compiler_Util.format1
                           "target effect is erasable but %s is neither erasable nor PURE"
                           uu___6 in
                       err uu___5
                     else ()))
               else ())
let (tc_polymonadic_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme ->
            (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.tscheme *
              FStar_Syntax_Syntax.indexed_effect_combinator_kind))
  =
  fun env ->
    fun m ->
      fun n ->
        fun p ->
          fun ts ->
            let eff_name =
              let uu___ =
                let uu___1 =
                  FStar_Compiler_Effect.op_Bar_Greater m
                    FStar_Ident.ident_of_lid in
                FStar_Compiler_Effect.op_Bar_Greater uu___1
                  FStar_Ident.string_of_id in
              let uu___1 =
                let uu___2 =
                  FStar_Compiler_Effect.op_Bar_Greater n
                    FStar_Ident.ident_of_lid in
                FStar_Compiler_Effect.op_Bar_Greater uu___2
                  FStar_Ident.string_of_id in
              let uu___2 =
                let uu___3 =
                  FStar_Compiler_Effect.op_Bar_Greater p
                    FStar_Ident.ident_of_lid in
                FStar_Compiler_Effect.op_Bar_Greater uu___3
                  FStar_Ident.string_of_id in
              FStar_Compiler_Util.format3 "(%s, %s) |> %s)" uu___ uu___1
                uu___2 in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
            check_polymonadic_bind_for_erasable_effects env m n p r;
            (let uu___1 =
               check_and_gen env eff_name "polymonadic_bind"
                 (Prims.of_int (2)) ts in
             match uu___1 with
             | (us, t, ty) ->
                 let uu___2 = FStar_Syntax_Subst.open_univ_vars us ty in
                 (match uu___2 with
                  | (us1, ty1) ->
                      let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                      let uu___3 =
                        let uu___4 =
                          FStar_TypeChecker_Env.get_effect_decl env1 m in
                        let uu___5 =
                          FStar_TypeChecker_Env.get_effect_decl env1 n in
                        let uu___6 =
                          FStar_TypeChecker_Env.get_effect_decl env1 p in
                        (uu___4, uu___5, uu___6) in
                      (match uu___3 with
                       | (m_ed, n_ed, p_ed) ->
                           let uu___4 =
                             let uu___5 = FStar_Syntax_Util.get_eff_repr m_ed in
                             let uu___6 = FStar_Syntax_Util.get_eff_repr n_ed in
                             let uu___7 = FStar_Syntax_Util.get_eff_repr p_ed in
                             let uu___8 =
                               FStar_TypeChecker_Env.get_range env1 in
                             validate_indexed_effect_bind_shape env1 m n p
                               m_ed.FStar_Syntax_Syntax.signature
                               n_ed.FStar_Syntax_Syntax.signature
                               p_ed.FStar_Syntax_Syntax.signature uu___5
                               uu___6 uu___7 us1 ty1 uu___8 false in
                           (match uu___4 with
                            | (k, kind) ->
                                ((let uu___6 =
                                    FStar_Compiler_Effect.op_Less_Bar
                                      (FStar_TypeChecker_Env.debug env1)
                                      FStar_Options.Extreme in
                                  if uu___6
                                  then
                                    let uu___7 =
                                      FStar_Syntax_Print.tscheme_to_string
                                        (us1, t) in
                                    let uu___8 =
                                      FStar_Syntax_Print.tscheme_to_string
                                        (us1, k) in
                                    FStar_Compiler_Util.print3
                                      "Polymonadic bind %s after typechecking (%s::%s)\n"
                                      eff_name uu___7 uu___8
                                  else ());
                                 (let uu___7 =
                                    let uu___8 =
                                      FStar_Compiler_Util.format1
                                        "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                        eff_name in
                                    (FStar_Errors.Warning_BleedingEdge_Feature,
                                      uu___8) in
                                  FStar_Errors.log_issue r uu___7);
                                 (let uu___7 =
                                    let uu___8 =
                                      FStar_Compiler_Effect.op_Bar_Greater k
                                        (FStar_Syntax_Subst.close_univ_vars
                                           us1) in
                                    (us1, uu___8) in
                                  ((us1, t), uu___7, kind)))))))
let (tc_polymonadic_subcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme ->
          (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.tscheme))
  =
  fun env0 ->
    fun m ->
      fun n ->
        fun ts ->
          let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
          check_lift_for_erasable_effects env0 m n r;
          (let combinator_name =
             let uu___1 =
               let uu___2 =
                 FStar_Compiler_Effect.op_Bar_Greater m
                   FStar_Ident.ident_of_lid in
               FStar_Compiler_Effect.op_Bar_Greater uu___2
                 FStar_Ident.string_of_id in
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   FStar_Compiler_Effect.op_Bar_Greater n
                     FStar_Ident.ident_of_lid in
                 FStar_Compiler_Effect.op_Bar_Greater uu___4
                   FStar_Ident.string_of_id in
               Prims.op_Hat " <: " uu___3 in
             Prims.op_Hat uu___1 uu___2 in
           let uu___1 =
             check_and_gen env0 combinator_name "polymonadic_subcomp"
               Prims.int_one ts in
           match uu___1 with
           | (us, t, ty) ->
               let uu___2 = FStar_Syntax_Subst.open_univ_vars us ty in
               (match uu___2 with
                | (us1, ty1) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                    let uu___4 =
                      let uu___5 = FStar_Syntax_Util.type_u () in
                      FStar_Compiler_Effect.op_Bar_Greater uu___5
                        (fun uu___6 ->
                           match uu___6 with
                           | (t1, u) ->
                               let uu___7 =
                                 let uu___8 =
                                   FStar_Syntax_Syntax.gen_bv "a"
                                     FStar_Pervasives_Native.None t1 in
                                 FStar_Compiler_Effect.op_Bar_Greater uu___8
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu___7, u)) in
                    (match uu___4 with
                     | (a, u) ->
                         let rest_bs =
                           let uu___5 =
                             let uu___6 = FStar_Syntax_Subst.compress ty1 in
                             uu___6.FStar_Syntax_Syntax.n in
                           match uu___5 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu___6) when
                               (FStar_Compiler_List.length bs) >=
                                 (Prims.of_int (2))
                               ->
                               let uu___7 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu___7 with
                                | { FStar_Syntax_Syntax.binder_bv = a';
                                    FStar_Syntax_Syntax.binder_qual = uu___8;
                                    FStar_Syntax_Syntax.binder_attrs = uu___9;_}::bs1
                                    ->
                                    let uu___10 =
                                      let uu___11 =
                                        FStar_Compiler_Effect.op_Bar_Greater
                                          bs1
                                          (FStar_Compiler_List.splitAt
                                             ((FStar_Compiler_List.length bs1)
                                                - Prims.int_one)) in
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        uu___11 FStar_Pervasives_Native.fst in
                                    let uu___11 =
                                      let uu___12 =
                                        let uu___13 =
                                          let uu___14 =
                                            let uu___15 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a.FStar_Syntax_Syntax.binder_bv in
                                            (a', uu___15) in
                                          FStar_Syntax_Syntax.NT uu___14 in
                                        [uu___13] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu___12 in
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      uu___10 uu___11)
                           | uu___6 ->
                               let uu___7 =
                                 let uu___8 =
                                   let uu___9 =
                                     FStar_Syntax_Print.tag_of_term t in
                                   let uu___10 =
                                     FStar_Syntax_Print.term_to_string t in
                                   FStar_Compiler_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu___9 uu___10 in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu___8) in
                               FStar_Errors.raise_error uu___7 r in
                         let bs = a :: rest_bs in
                         let uu___5 =
                           let uu___6 =
                             let uu___7 =
                               FStar_TypeChecker_Env.push_binders env bs in
                             let uu___8 =
                               FStar_Compiler_Effect.op_Bar_Greater
                                 a.FStar_Syntax_Syntax.binder_bv
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu___7 r m u uu___8 in
                           match uu___6 with
                           | (repr, g) ->
                               let uu___7 =
                                 let uu___8 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr in
                                 FStar_Compiler_Effect.op_Bar_Greater uu___8
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu___7, g) in
                         (match uu___5 with
                          | (f, guard_f) ->
                              let uu___6 =
                                let uu___7 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu___8 =
                                  FStar_Compiler_Effect.op_Bar_Greater
                                    a.FStar_Syntax_Syntax.binder_bv
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu___7 r n u uu___8 in
                              (match uu___6 with
                               | (ret_t, guard_ret_t) ->
                                   let uu___7 =
                                     let uu___8 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu___9 =
                                       FStar_Compiler_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name in
                                     pure_wp_uvar uu___8 ret_t uu___9 r in
                                   (match uu___7 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu___8 =
                                            let uu___9 =
                                              let uu___10 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu___10] in
                                            let uu___10 =
                                              let uu___11 =
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu___11] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu___9;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu___10;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp uu___8 in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_Compiler_List.op_At bs [f])
                                            c in
                                        ((let uu___9 =
                                            FStar_Compiler_Effect.op_Less_Bar
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu___9
                                          then
                                            let uu___10 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Compiler_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu___10
                                          else ());
                                         (let guard_eq =
                                            FStar_TypeChecker_Rel.teq env ty1
                                              k in
                                          FStar_Compiler_List.iter
                                            (FStar_TypeChecker_Rel.force_trivial_guard
                                               env)
                                            [guard_f;
                                            guard_ret_t;
                                            guard_wp;
                                            guard_eq];
                                          (let k1 =
                                             let uu___10 =
                                               FStar_Compiler_Effect.op_Bar_Greater
                                                 k
                                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                    env) in
                                             FStar_Compiler_Effect.op_Bar_Greater
                                               uu___10
                                               (FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.Beta;
                                                  FStar_TypeChecker_Env.Eager_unfolding]
                                                  env) in
                                           (let uu___11 =
                                              FStar_Compiler_Effect.op_Less_Bar
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu___11
                                            then
                                              let uu___12 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1) in
                                              FStar_Compiler_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu___12
                                            else ());
                                           (let check_non_informative_binders
                                              =
                                              (FStar_TypeChecker_Env.is_reifiable_effect
                                                 env n)
                                                &&
                                                (let uu___11 =
                                                   FStar_TypeChecker_Env.fv_with_lid_has_attr
                                                     env n
                                                     FStar_Parser_Const.allow_informative_binders_attr in
                                                 Prims.op_Negation uu___11) in
                                            (let uu___11 =
                                               let uu___12 =
                                                 FStar_Syntax_Subst.compress
                                                   k1 in
                                               uu___12.FStar_Syntax_Syntax.n in
                                             match uu___11 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs1, c1) ->
                                                 let uu___12 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs1 c1 in
                                                 (match uu___12 with
                                                  | (a1::bs2, c2) ->
                                                      let res_t =
                                                        FStar_Syntax_Util.comp_result
                                                          c2 in
                                                      let uu___13 =
                                                        let uu___14 =
                                                          FStar_Compiler_List.splitAt
                                                            ((FStar_Compiler_List.length
                                                                bs2)
                                                               -
                                                               Prims.int_one)
                                                            bs2 in
                                                        FStar_Compiler_Effect.op_Bar_Greater
                                                          uu___14
                                                          (fun uu___15 ->
                                                             match uu___15
                                                             with
                                                             | (l1, l2) ->
                                                                 let uu___16
                                                                   =
                                                                   FStar_Compiler_List.hd
                                                                    l2 in
                                                                 (l1,
                                                                   uu___16)) in
                                                      (match uu___13 with
                                                       | (bs3, f_b) ->
                                                           let env1 =
                                                             FStar_TypeChecker_Env.push_binders
                                                               env [a1] in
                                                           validate_layered_effect_binders
                                                             env1 bs3
                                                             check_non_informative_binders
                                                             r)));
                                            (let uu___12 =
                                               let uu___13 =
                                                 FStar_Compiler_Util.format1
                                                   "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                   combinator_name in
                                               (FStar_Errors.Warning_BleedingEdge_Feature,
                                                 uu___13) in
                                             FStar_Errors.log_issue r uu___12);
                                            (let uu___12 =
                                               let uu___13 =
                                                 FStar_Compiler_Effect.op_Bar_Greater
                                                   k1
                                                   (FStar_Syntax_Subst.close_univ_vars
                                                      us1) in
                                               (us1, uu___13) in
                                             ((us1, t), uu___12))))))))))))