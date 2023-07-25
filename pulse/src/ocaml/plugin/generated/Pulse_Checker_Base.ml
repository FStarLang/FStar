open Prims
let (format_failed_goal :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term Prims.list ->
      Pulse_Syntax_Base.term Prims.list ->
        (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun goal ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                   (Prims.of_int (14)) (Prims.of_int (39))
                   (Prims.of_int (14)) (Prims.of_int (83)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                   (Prims.of_int (14)) (Prims.of_int (86))
                   (Prims.of_int (29)) (Prims.of_int (21)))))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun ts ->
                  FStar_Tactics_Util.map Pulse_Syntax_Printer.term_to_string
                    ts))
          (fun uu___ ->
             (fun terms_to_strings ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                              (Prims.of_int (15)) (Prims.of_int (24))
                              (Prims.of_int (17)) (Prims.of_int (40)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                              (Prims.of_int (18)) (Prims.of_int (4))
                              (Prims.of_int (29)) (Prims.of_int (21)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           fun ss ->
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (16))
                                        (Prims.of_int (18))
                                        (Prims.of_int (16))
                                        (Prims.of_int (102)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (15))
                                        (Prims.of_int (24))
                                        (Prims.of_int (17))
                                        (Prims.of_int (40)))))
                               (Obj.magic
                                  (FStar_Tactics_Util.fold_left
                                     (fun uu___2 ->
                                        fun uu___1 ->
                                          (fun uu___1 ->
                                             fun s ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
                                                       match uu___1 with
                                                       | (i, acc) ->
                                                           ((i +
                                                               Prims.int_one),
                                                             ((Prims.strcat
                                                                 (Prims.strcat
                                                                    ""
                                                                    (
                                                                    Prims.strcat
                                                                    (Prims.string_of_int
                                                                    i) ". "))
                                                                 (Prims.strcat
                                                                    s "")) ::
                                                             acc))))) uu___2
                                            uu___1) (Prims.int_one, []) ss))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       match uu___1 with
                                       | (uu___3, s) ->
                                           FStar_String.concat "\n  "
                                             (FStar_List_Tot_Base.rev s)))))
                     (fun uu___ ->
                        (fun numbered_list ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Base.fst"
                                         (Prims.of_int (19))
                                         (Prims.of_int (36))
                                         (Prims.of_int (19))
                                         (Prims.of_int (71)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Base.fst"
                                         (Prims.of_int (20))
                                         (Prims.of_int (2))
                                         (Prims.of_int (29))
                                         (Prims.of_int (21)))))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      fun ts ->
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (50))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (71)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (36))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (71)))))
                                          (Obj.magic (terms_to_strings ts))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                Obj.magic
                                                  (numbered_list uu___1))
                                               uu___1)))
                                (fun uu___ ->
                                   (fun format_terms ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Base.fst"
                                                    (Prims.of_int (29))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (29))
                                                    (Prims.of_int (21)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Base.fst"
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (29))
                                                    (Prims.of_int (21)))))
                                           (Obj.magic
                                              (Pulse_Typing_Env.env_to_string
                                                 g))
                                           (fun uu___ ->
                                              (fun uu___ ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Base.fst"
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (29))
                                                               (Prims.of_int (21)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Base.fst"
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (29))
                                                               (Prims.of_int (21)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (23)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (21)))))
                                                            (Obj.magic
                                                               (format_terms
                                                                  ctxt))
                                                            (fun uu___1 ->
                                                               (fun uu___1 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (format_terms
                                                                    goal))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Failed to prove the following goals:\n  "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    "\nThe remaining conjuncts in the separation logic context available for use are:\n  "))
                                                                    (Prims.strcat
                                                                    x
                                                                    "\nThe typing context is:\n  "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2
                                                                    uu___1))))
                                                                 uu___1)))
                                                      (fun uu___1 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___2 ->
                                                              uu___1 uu___))))
                                                uu___))) uu___))) uu___)))
               uu___)
let (mk_arrow :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun t ->
      FStar_Reflection_Typing.mk_arrow (Pulse_Elaborate_Pure.elab_term ty)
        FStar_Reflection_V2_Data.Q_Explicit
        (Pulse_Elaborate_Pure.elab_term t)
let (mk_abs :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun t ->
      FStar_Reflection_Typing.mk_abs (Pulse_Elaborate_Pure.elab_term ty)
        FStar_Reflection_V2_Data.Q_Explicit
        (Pulse_Elaborate_Pure.elab_term t)
let (intro_post_hint :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.ctag FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
        Pulse_Syntax_Base.term ->
          (unit Pulse_Typing.post_hint_for_env, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctag_opt ->
      fun ret_ty_opt ->
        fun post ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                     (Prims.of_int (42)) (Prims.of_int (10))
                     (Prims.of_int (42)) (Prims.of_int (17)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                     (Prims.of_int (42)) (Prims.of_int (20))
                     (Prims.of_int (54)) (Prims.of_int (129)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> Pulse_Typing_Env.fresh g))
            (fun uu___ ->
               (fun x ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                                (Prims.of_int (44)) (Prims.of_int (6))
                                (Prims.of_int (46)) (Prims.of_int (19)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                                (Prims.of_int (47)) (Prims.of_int (4))
                                (Prims.of_int (54)) (Prims.of_int (129)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             match ret_ty_opt with
                             | FStar_Pervasives_Native.None ->
                                 Pulse_Syntax_Base.tm_fstar
                                   FStar_Reflection_Typing.unit_ty
                                   FStar_Range.range_0
                             | FStar_Pervasives_Native.Some t -> t))
                       (fun uu___ ->
                          (fun ret_ty ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Base.fst"
                                           (Prims.of_int (48))
                                           (Prims.of_int (18))
                                           (Prims.of_int (48))
                                           (Prims.of_int (56)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Base.fst"
                                           (Prims.of_int (47))
                                           (Prims.of_int (4))
                                           (Prims.of_int (54))
                                           (Prims.of_int (129)))))
                                  (Obj.magic
                                     (Pulse_Checker_Pure.instantiate_term_implicits
                                        g ret_ty))
                                  (fun uu___ ->
                                     (fun uu___ ->
                                        match uu___ with
                                        | (ret_ty1, uu___1) ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Base.fst"
                                                          (Prims.of_int (49))
                                                          (Prims.of_int (27))
                                                          (Prims.of_int (49))
                                                          (Prims.of_int (53)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Base.fst"
                                                          (Prims.of_int (48))
                                                          (Prims.of_int (59))
                                                          (Prims.of_int (54))
                                                          (Prims.of_int (129)))))
                                                 (Obj.magic
                                                    (Pulse_Checker_Pure.check_universe
                                                       g ret_ty1))
                                                 (fun uu___2 ->
                                                    (fun uu___2 ->
                                                       match uu___2 with
                                                       | Prims.Mkdtuple2
                                                           (u, ty_typing) ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (119)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (129)))))
                                                                (Obj.magic
                                                                   (Pulse_Checker_Pure.check_vprop
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    ret_ty1)
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    post
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    x))))
                                                                (fun uu___3
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post1,
                                                                    post_typing)
                                                                    ->
                                                                    {
                                                                    Pulse_Typing.g
                                                                    = g;
                                                                    Pulse_Typing.ctag_hint
                                                                    =
                                                                    ctag_opt;
                                                                    Pulse_Typing.ret_ty
                                                                    = ret_ty1;
                                                                    Pulse_Typing.u
                                                                    = u;
                                                                    Pulse_Typing.ty_typing
                                                                    = ();
                                                                    Pulse_Typing.post
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post1 x);
                                                                    Pulse_Typing.post_typing
                                                                    = ()
                                                                    }))))
                                                      uu___2))) uu___)))
                            uu___))) uu___)
let (post_hint_from_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit) Pulse_Typing_Metatheory.comp_typing_u ->
        unit Pulse_Typing.post_hint_for_env)
  =
  fun g ->
    fun c ->
      fun ct ->
        let st_comp_typing =
          Pulse_Typing_Metatheory.comp_typing_inversion g c ct in
        let uu___ =
          Pulse_Typing_Metatheory.st_comp_typing_inversion g
            (Pulse_Syntax_Base.st_comp_of_comp c) st_comp_typing in
        match uu___ with
        | FStar_Pervasives.Mkdtuple4 (ty_typing, pre_typing, x, post_typing)
            ->
            let p =
              {
                Pulse_Typing.g = g;
                Pulse_Typing.ctag_hint =
                  (FStar_Pervasives_Native.Some
                     (Pulse_Syntax_Base.ctag_of_comp_st c));
                Pulse_Typing.ret_ty = (Pulse_Syntax_Base.comp_res c);
                Pulse_Typing.u = (Pulse_Syntax_Base.comp_u c);
                Pulse_Typing.ty_typing = ();
                Pulse_Typing.post = (Pulse_Syntax_Base.comp_post c);
                Pulse_Typing.post_typing = ()
              } in
            p
type ('g, 'ctxt, 'gu, 'ctxtu) continuation_elaborator =
  unit Pulse_Typing.post_hint_opt ->
    (unit, unit, unit) Pulse_Typing_Combinators.st_typing_in_ctxt ->
      ((unit, unit, unit) Pulse_Typing_Combinators.st_typing_in_ctxt, 
        unit) FStar_Tactics_Effect.tac_repr
let (k_elab_unit :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (unit, unit, unit, unit) continuation_elaborator)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun ctxt ->
           fun p ->
             fun r ->
               Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> r)))
        uu___1 uu___
let (k_elab_trans :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Typing_Env.env ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit) continuation_elaborator ->
                (unit, unit, unit, unit) continuation_elaborator ->
                  (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g0 ->
    fun g1 ->
      fun g2 ->
        fun ctxt0 ->
          fun ctxt1 ->
            fun ctxt2 ->
              fun k0 ->
                fun k1 ->
                  fun post_hint ->
                    fun res ->
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                                 (Prims.of_int (78)) (Prims.of_int (39))
                                 (Prims.of_int (78)) (Prims.of_int (57)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                                 (Prims.of_int (78)) (Prims.of_int (26))
                                 (Prims.of_int (78)) (Prims.of_int (57)))))
                        (Obj.magic (k1 post_hint res))
                        (fun uu___ ->
                           (fun uu___ -> Obj.magic (k0 post_hint uu___))
                             uu___)
let (comp_st_with_post :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp_st)
  =
  fun c ->
    fun post ->
      match c with
      | Pulse_Syntax_Base.C_ST st ->
          Pulse_Syntax_Base.C_ST
            {
              Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
              Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
              Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
              Pulse_Syntax_Base.post = post
            }
      | Pulse_Syntax_Base.C_STGhost (i, st) ->
          Pulse_Syntax_Base.C_STGhost
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
                Pulse_Syntax_Base.post = post
              })
      | Pulse_Syntax_Base.C_STAtomic (i, st) ->
          Pulse_Syntax_Base.C_STAtomic
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
                Pulse_Syntax_Base.post = post
              })
let (st_equiv_post :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.term ->
            unit -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t ->
      fun c ->
        fun d ->
          fun post ->
            fun veq ->
              let c' = comp_st_with_post c post in
              let uu___ =
                Pulse_Typing_Metatheory.st_comp_typing_inversion g
                  (Pulse_Syntax_Base.st_comp_of_comp c)
                  (Pulse_Typing_Metatheory.comp_typing_inversion g c
                     (Pulse_Typing_Metatheory.st_typing_correctness g t c d)) in
              match uu___ with
              | FStar_Pervasives.Mkdtuple4 (u_of, pre_typing, x, post_typing)
                  ->
                  let st_equiv =
                    Pulse_Typing.ST_VPropEquiv
                      (g, c, c', x, (), (), (), (), ()) in
                  Pulse_Typing.T_Equiv (g, t, c, c', d, st_equiv)
let (simplify_post :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.term -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t -> fun c -> fun d -> fun post -> st_equiv_post g t c d post ()

let (k_elab_equiv_continutation :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            (unit, unit, unit, unit) continuation_elaborator ->
              unit -> (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g1 ->
    fun g2 ->
      fun ctxt ->
        fun ctxt1 ->
          fun ctxt2 ->
            fun k ->
              fun d ->
                fun post_hint ->
                  fun res ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                               (Prims.of_int (134)) (Prims.of_int (60))
                               (Prims.of_int (137)) (Prims.of_int (33)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                               (Prims.of_int (138)) (Prims.of_int (4))
                               (Prims.of_int (146)) (Prims.of_int (32)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ ->
                            FStar_Pervasives.Mkdtuple3
                              (Pulse_Syntax_Base.tm_emp, (), ())))
                      (fun uu___ ->
                         (fun framing_token ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Base.fst"
                                          (Prims.of_int (139))
                                          (Prims.of_int (26))
                                          (Prims.of_int (139))
                                          (Prims.of_int (29)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Base.fst"
                                          (Prims.of_int (138))
                                          (Prims.of_int (4))
                                          (Prims.of_int (146))
                                          (Prims.of_int (32)))))
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ -> res))
                                 (fun uu___ ->
                                    (fun uu___ ->
                                       match uu___ with
                                       | FStar_Pervasives.Mkdtuple3
                                           (st, c, st_d) ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Base.fst"
                                                         (Prims.of_int (141))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (141))
                                                         (Prims.of_int (93)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Base.fst"
                                                         (Prims.of_int (139))
                                                         (Prims.of_int (32))
                                                         (Prims.of_int (146))
                                                         (Prims.of_int (32)))))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___1 ->
                                                      Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                        g2
                                                        (Pulse_Syntax_Base.st_comp_of_comp
                                                           c)
                                                        (Pulse_Typing_Metatheory.comp_typing_inversion
                                                           g2 c
                                                           (Pulse_Typing_Metatheory.st_typing_correctness
                                                              g2 st c st_d))))
                                                (fun uu___1 ->
                                                   (fun uu___1 ->
                                                      match uu___1 with
                                                      | FStar_Pervasives.Mkdtuple4
                                                          (uu___2,
                                                           pre_typing,
                                                           uu___3, uu___4)
                                                          ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (71)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (32)))))
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___5
                                                                    ->
                                                                    Pulse_Typing_Combinators.apply_frame
                                                                    g2 st
                                                                    ctxt1 ()
                                                                    c st_d
                                                                    framing_token))
                                                               (fun uu___5 ->
                                                                  (fun uu___5
                                                                    ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c',
                                                                    st_d') ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    simplify_post
                                                                    g2 st c'
                                                                    st_d'
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    st_d'1 ->
                                                                    Obj.magic
                                                                    (k
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (st,
                                                                    (comp_st_with_post
                                                                    c'
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)),
                                                                    st_d'1))))
                                                                    uu___6)))
                                                                    uu___5)))
                                                     uu___1))) uu___))) uu___)

let (k_elab_equiv_prefix :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            (unit, unit, unit, unit) continuation_elaborator ->
              unit -> (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g1 ->
    fun g2 ->
      fun ctxt1 ->
        fun ctxt2 ->
          fun ctxt ->
            fun k ->
              fun d ->
                fun post_hint ->
                  fun res ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                               (Prims.of_int (162)) (Prims.of_int (60))
                               (Prims.of_int (164)) (Prims.of_int (31)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                               (Prims.of_int (165)) (Prims.of_int (4))
                               (Prims.of_int (179)) (Prims.of_int (5)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ ->
                            FStar_Pervasives.Mkdtuple3
                              (Pulse_Syntax_Base.tm_emp, (), ())))
                      (fun uu___ ->
                         (fun framing_token ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Base.fst"
                                          (Prims.of_int (166))
                                          (Prims.of_int (12))
                                          (Prims.of_int (166))
                                          (Prims.of_int (27)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Base.fst"
                                          (Prims.of_int (166))
                                          (Prims.of_int (30))
                                          (Prims.of_int (179))
                                          (Prims.of_int (5)))))
                                 (Obj.magic (k post_hint res))
                                 (fun res1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ ->
                                         match res1 with
                                         | FStar_Pervasives.Mkdtuple3
                                             (st, c, st_d) ->
                                             (match Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                      g1
                                                      (Pulse_Syntax_Base.st_comp_of_comp
                                                         c)
                                                      (Pulse_Typing_Metatheory.comp_typing_inversion
                                                         g1 c
                                                         (Pulse_Typing_Metatheory.st_typing_correctness
                                                            g1 st c st_d))
                                              with
                                              | FStar_Pervasives.Mkdtuple4
                                                  (uu___1, pre_typing,
                                                   uu___2, uu___3)
                                                  ->
                                                  (match Pulse_Typing_Combinators.apply_frame
                                                           g1 st ctxt2 () c
                                                           st_d framing_token
                                                   with
                                                   | Prims.Mkdtuple2
                                                       (c', st_d') ->
                                                       FStar_Pervasives.Mkdtuple3
                                                         (st,
                                                           (comp_st_with_post
                                                              c'
                                                              (Pulse_Syntax_Base.comp_post
                                                                 c)),
                                                           (simplify_post g1
                                                              st c' st_d'
                                                              (Pulse_Syntax_Base.comp_post
                                                                 c)))))))))
                           uu___)
let (k_elab_equiv :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit) continuation_elaborator ->
                unit ->
                  unit -> (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g1 ->
    fun g2 ->
      fun ctxt1 ->
        fun ctxt1' ->
          fun ctxt2 ->
            fun ctxt2' ->
              fun k ->
                fun d1 ->
                  fun d2 ->
                    let k1 =
                      k_elab_equiv_continutation g1 g2 ctxt1 ctxt2 ctxt2' k
                        () in
                    let k2 =
                      k_elab_equiv_prefix g1 g2 ctxt1 ctxt1' ctxt2' k1 () in
                    k2
let (continuation_elaborator_with_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.st_term ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            unit ->
              Pulse_Syntax_Base.var ->
                ((unit, unit, unit, unit) continuation_elaborator, unit)
                  FStar_Tactics_Effect.tac_repr)
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun g ->
                   fun ctxt ->
                     fun c1 ->
                       fun e1 ->
                         fun e1_typing ->
                           fun ctxt_pre1_typing ->
                             fun x ->
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ ->
                                       match Pulse_Typing_Combinators.apply_frame
                                               g e1
                                               (Pulse_Syntax_Base.tm_star
                                                  ctxt
                                                  (Pulse_Syntax_Base.comp_pre
                                                     c1)) () c1 e1_typing
                                               (FStar_Pervasives.Mkdtuple3
                                                  (ctxt, (), ()))
                                       with
                                       | Prims.Mkdtuple2 (c11, e1_typing1) ->
                                           (match Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                    g
                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                       c11)
                                                    (Pulse_Typing_Metatheory.comp_typing_inversion
                                                       g c11
                                                       (Pulse_Typing_Metatheory.st_typing_correctness
                                                          g e1 c11 e1_typing1))
                                            with
                                            | FStar_Pervasives.Mkdtuple4
                                                (u_of_1, pre_typing, uu___1,
                                                 uu___2)
                                                ->
                                                (fun post_hint ->
                                                   fun res ->
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Base.fst"
                                                                (Prims.of_int (225))
                                                                (Prims.of_int (34))
                                                                (Prims.of_int (225))
                                                                (Prims.of_int (37)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Base.fst"
                                                                (Prims.of_int (224))
                                                                (Prims.of_int (24))
                                                                (Prims.of_int (253))
                                                                (Prims.of_int (5)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 -> res))
                                                       (fun uu___3 ->
                                                          (fun uu___3 ->
                                                             match uu___3
                                                             with
                                                             | FStar_Pervasives.Mkdtuple3
                                                                 (e2, c2,
                                                                  e2_typing)
                                                                 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    e2_typing))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    e2_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    e2 x))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    e2_closed
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c2))
                                                                    then
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1))
                                                                    FStar_Pervasives_Native.None
                                                                    "Impossible: freevar clash when constructing continuation elaborator for bind, please file a bug-report")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Combinators.bind_res_and_post_typing
                                                                    g
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2) x
                                                                    post_hint))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (t_typing,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Combinators.mk_bind
                                                                    g
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c1)) e1
                                                                    e2_closed
                                                                    c11 c2
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    x)
                                                                    e1_typing1
                                                                    ()
                                                                    e2_typing1
                                                                    () ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e, c,
                                                                    e_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e, c,
                                                                    e_typing)))))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                            uu___3))))))
                  uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (continuation_elaborator_with_tot_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Syntax_Base.var ->
                ((unit, unit, unit, unit) continuation_elaborator, unit)
                  FStar_Tactics_Effect.tac_repr)
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun g ->
                   fun ctxt ->
                     fun ctxt_typing ->
                       fun e1 ->
                         fun t1 ->
                           fun e1_typing ->
                             fun x ->
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ ->
                                       (fun uu___ ->
                                          fun post_hint ->
                                            fun uu___1 ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      match uu___1 with
                                                      | FStar_Pervasives.Mkdtuple3
                                                          (e2, c2, d2) ->
                                                          FStar_Pervasives.Mkdtuple3
                                                            ((Pulse_Typing.wr
                                                                (Pulse_Syntax_Base.Tm_TotBind
                                                                   {
                                                                    Pulse_Syntax_Base.head2
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body2
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    e2 x)
                                                                   })),
                                                              (Pulse_Syntax_Naming.open_comp_with
                                                                 (Pulse_Syntax_Naming.close_comp
                                                                    c2 x) e1),
                                                              (Pulse_Typing.T_TotBind
                                                                 (g, e1,
                                                                   (Pulse_Syntax_Naming.close_st_term
                                                                    e2 x),
                                                                   t1, c2, x,
                                                                   (), d2))))))
                                         uu___))) uu___6 uu___5 uu___4 uu___3
                  uu___2 uu___1 uu___
let rec (check_equiv_emp :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term -> unit FStar_Pervasives_Native.option)
  =
  fun g ->
    fun vp ->
      match vp.Pulse_Syntax_Base.t with
      | Pulse_Syntax_Base.Tm_Emp -> FStar_Pervasives_Native.Some ()
      | Pulse_Syntax_Base.Tm_Star (vp1, vp2) ->
          (match ((check_equiv_emp g vp1), (check_equiv_emp g vp2)) with
           | (FStar_Pervasives_Native.Some d1, FStar_Pervasives_Native.Some
              d2) -> FStar_Pervasives_Native.Some ()
           | (uu___, uu___1) -> FStar_Pervasives_Native.None)
      | uu___ -> FStar_Pervasives_Native.None
type ('g, 'postuhint, 'x, 't, 'ctxtu) checker_res_matches_post_hint = Obj.t
type ('g, 'postuhint, 'x, 'g1, 't, 'ctxtu) checker_result_inv = Obj.t
type ('g, 'ctxt, 'postuhint) checker_result_t =
  (Pulse_Syntax_Base.var, Pulse_Typing_Env.env,
    (Pulse_Syntax_Base.universe, Pulse_Syntax_Base.typ, unit)
      FStar_Pervasives.dtuple3,
    (Pulse_Syntax_Base.vprop, unit) Prims.dtuple2,
    (unit, unit, unit, unit) continuation_elaborator)
    FStar_Pervasives.dtuple5
type check_t =
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.st_term ->
            ((unit, unit, unit) checker_result_t, unit)
              FStar_Tactics_Effect.tac_repr
let (intro_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      unit ->
        unit ->
          Pulse_Syntax_Base.var ->
            unit ->
              ((unit, unit, unit) Pulse_Typing.comp_typing, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun c ->
      fun pre_typing ->
        fun res_typing ->
          fun x ->
            fun post_typing ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                         (Prims.of_int (330)) (Prims.of_int (8))
                         (Prims.of_int (330)) (Prims.of_int (52)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                         (Prims.of_int (332)) (Prims.of_int (4))
                         (Prims.of_int (347)) (Prims.of_int (44)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      fun uu___ ->
                        (fun uu___ ->
                           fun st ->
                             Obj.magic
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     Pulse_Typing.STC (g, st, x, (), (), ()))))
                          uu___1 uu___))
                (fun uu___ ->
                   (fun intro_st_comp_typing ->
                      match c with
                      | Pulse_Syntax_Base.C_ST st ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (334))
                                        (Prims.of_int (16))
                                        (Prims.of_int (334))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (335))
                                        (Prims.of_int (6))
                                        (Prims.of_int (335))
                                        (Prims.of_int (19)))))
                               (Obj.magic (intro_st_comp_typing st))
                               (fun stc ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ ->
                                       Pulse_Typing.CT_ST (g, st, stc))))
                      | Pulse_Syntax_Base.C_STAtomic (i, st) ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (337))
                                        (Prims.of_int (16))
                                        (Prims.of_int (337))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (337))
                                        (Prims.of_int (42))
                                        (Prims.of_int (341))
                                        (Prims.of_int (45)))))
                               (Obj.magic (intro_st_comp_typing st))
                               (fun uu___ ->
                                  (fun stc ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (338))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (338))
                                                   (Prims.of_int (53)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (337))
                                                   (Prims.of_int (42))
                                                   (Prims.of_int (341))
                                                   (Prims.of_int (45)))))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.core_check_term
                                                g i))
                                          (fun uu___ ->
                                             (fun uu___ ->
                                                match uu___ with
                                                | Prims.Mkdtuple2
                                                    (ty, i_typing) ->
                                                    if
                                                      Prims.op_Negation
                                                        (Pulse_Syntax_Base.eq_tm
                                                           ty
                                                           Pulse_Syntax_Base.tm_inames)
                                                    then
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (87)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (87)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (86)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (
                                                                    Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    i))
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Prims.strcat
                                                                    "ill-typed inames term "
                                                                    (Prims.strcat
                                                                    uu___1 "")))))
                                                              (fun uu___1 ->
                                                                 (fun uu___1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    uu___1))
                                                                   uu___1)))
                                                    else
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 Pulse_Typing.CT_STAtomic
                                                                   (g, i, st,
                                                                    (), stc)))))
                                               uu___))) uu___))
                      | Pulse_Syntax_Base.C_STGhost (i, st) ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (343))
                                        (Prims.of_int (16))
                                        (Prims.of_int (343))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (343))
                                        (Prims.of_int (42))
                                        (Prims.of_int (347))
                                        (Prims.of_int (44)))))
                               (Obj.magic (intro_st_comp_typing st))
                               (fun uu___ ->
                                  (fun stc ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (344))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (344))
                                                   (Prims.of_int (53)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (343))
                                                   (Prims.of_int (42))
                                                   (Prims.of_int (347))
                                                   (Prims.of_int (44)))))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.core_check_term
                                                g i))
                                          (fun uu___ ->
                                             (fun uu___ ->
                                                match uu___ with
                                                | Prims.Mkdtuple2
                                                    (ty, i_typing) ->
                                                    if
                                                      Prims.op_Negation
                                                        (Pulse_Syntax_Base.eq_tm
                                                           ty
                                                           Pulse_Syntax_Base.tm_inames)
                                                    then
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (87)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (87)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (86)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (
                                                                    Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    i))
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Prims.strcat
                                                                    "ill-typed inames term "
                                                                    (Prims.strcat
                                                                    uu___1 "")))))
                                                              (fun uu___1 ->
                                                                 (fun uu___1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    uu___1))
                                                                   uu___1)))
                                                    else
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 Pulse_Typing.CT_STGhost
                                                                   (g, i, st,
                                                                    (), stc)))))
                                               uu___))) uu___))) uu___)
let (return_in_ctxt :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.universe ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              unit Pulse_Typing.post_hint_opt ->
                (unit, unit, unit) Pulse_Typing_Combinators.st_typing_in_ctxt)
  =
  fun g ->
    fun y ->
      fun u ->
        fun ty ->
          fun ctxt ->
            fun ty_typing ->
              fun post_hint0 ->
                let uu___ = post_hint0 in
                match uu___ with
                | FStar_Pervasives_Native.Some post_hint ->
                    let x = Pulse_Typing_Env.fresh g in
                    let ctag =
                      match post_hint.Pulse_Typing.ctag_hint with
                      | FStar_Pervasives_Native.None -> Pulse_Syntax_Base.STT
                      | FStar_Pervasives_Native.Some ctag1 -> ctag1 in
                    let d =
                      Pulse_Typing.T_Return
                        (g, ctag, false, u, ty,
                          (Pulse_Syntax_Pure.null_var y),
                          (post_hint.Pulse_Typing.post), x, (), (), ()) in
                    let t =
                      Pulse_Typing.wr
                        (Pulse_Syntax_Base.Tm_Return
                           {
                             Pulse_Syntax_Base.ctag = ctag;
                             Pulse_Syntax_Base.insert_eq = false;
                             Pulse_Syntax_Base.term =
                               (Pulse_Syntax_Pure.null_var y)
                           }) in
                    let c =
                      Pulse_Typing.comp_return ctag false u ty
                        (Pulse_Syntax_Pure.null_var y)
                        post_hint.Pulse_Typing.post x in
                    let d1 = d in FStar_Pervasives.Mkdtuple3 (t, c, d1)
let (apply_checker_result_k :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit Pulse_Typing.post_hint_for_env ->
        (unit, unit, unit) checker_result_t ->
          ((unit, unit, unit) Pulse_Typing_Combinators.st_typing_in_ctxt,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun post_hint ->
        fun r ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                     (Prims.of_int (386)) (Prims.of_int (64))
                     (Prims.of_int (386)) (Prims.of_int (65)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                     (Prims.of_int (383)) (Prims.of_int (55))
                     (Prims.of_int (393)) (Prims.of_int (22)))))
            (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> r))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | FStar_Pervasives.Mkdtuple5
                      (y, g1, FStar_Pervasives.Mkdtuple3
                       (u_ty, ty_y, d_ty_y), Prims.Mkdtuple2 (pre', uu___1),
                       k)
                      ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Base.fst"
                                    (Prims.of_int (388)) (Prims.of_int (29))
                                    (Prims.of_int (388)) (Prims.of_int (70)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Base.fst"
                                    (Prims.of_int (386)) (Prims.of_int (68))
                                    (Prims.of_int (393)) (Prims.of_int (22)))))
                           (Obj.magic
                              (Pulse_Checker_Pure.check_universe g1 ty_y))
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 match uu___2 with
                                 | Prims.Mkdtuple2 (u_ty_y, d_ty_y1) ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (391))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (391))
                                                   (Prims.of_int (64)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (393))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (393))
                                                   (Prims.of_int (22)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                return_in_ctxt g1 y u_ty_y
                                                  ty_y pre' ()
                                                  (FStar_Pervasives_Native.Some
                                                     post_hint)))
                                          (fun uu___3 ->
                                             (fun d ->
                                                Obj.magic
                                                  (k
                                                     (FStar_Pervasives_Native.Some
                                                        post_hint) d)) uu___3)))
                                uu___2))) uu___)
let (checker_result_for_st_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit Pulse_Typing.post_hint_opt ->
        (unit, unit, unit) Pulse_Typing_Combinators.st_typing_in_ctxt ->
          ((unit, unit, unit) checker_result_t, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun post_hint ->
        fun d ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                     (Prims.of_int (400)) (Prims.of_int (22))
                     (Prims.of_int (400)) (Prims.of_int (23)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                     (Prims.of_int (398)) (Prims.of_int (47))
                     (Prims.of_int (429)) (Prims.of_int (72)))))
            (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> d))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | FStar_Pervasives.Mkdtuple3 (t, c, d1) ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Base.fst"
                                    (Prims.of_int (402)) (Prims.of_int (10))
                                    (Prims.of_int (402)) (Prims.of_int (17)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Base.fst"
                                    (Prims.of_int (402)) (Prims.of_int (20))
                                    (Prims.of_int (429)) (Prims.of_int (72)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> Pulse_Typing_Env.fresh g))
                           (fun uu___1 ->
                              (fun x ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Base.fst"
                                               (Prims.of_int (404))
                                               (Prims.of_int (11))
                                               (Prims.of_int (404))
                                               (Prims.of_int (55)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Base.fst"
                                               (Prims.of_int (404))
                                               (Prims.of_int (58))
                                               (Prims.of_int (429))
                                               (Prims.of_int (72)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            Pulse_Typing_Env.push_binding g x
                                              Pulse_Syntax_Base.ppname_default
                                              (Pulse_Syntax_Base.comp_res c)))
                                      (fun uu___1 ->
                                         (fun g' ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Base.fst"
                                                          (Prims.of_int (405))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (405))
                                                          (Prims.of_int (60)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Base.fst"
                                                          (Prims.of_int (405))
                                                          (Prims.of_int (63))
                                                          (Prims.of_int (429))
                                                          (Prims.of_int (72)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       Pulse_Syntax_Naming.open_term_nv
                                                         (Pulse_Syntax_Base.comp_post
                                                            c)
                                                         (Pulse_Syntax_Base.ppname_default,
                                                           x)))
                                                 (fun uu___1 ->
                                                    (fun ctxt' ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (59)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (72)))))
                                                            (Obj.magic
                                                               (continuation_elaborator_with_bind
                                                                  g
                                                                  Pulse_Syntax_Base.tm_emp
                                                                  c t d1 () x))
                                                            (fun k ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___1
                                                                    ->
                                                                    match 
                                                                    Pulse_Typing_Metatheory.st_comp_typing_inversion_cofinite
                                                                    g
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c)
                                                                    (Pulse_Typing_Metatheory.comp_typing_inversion
                                                                    g c
                                                                    (Pulse_Typing_Metatheory.st_typing_correctness
                                                                    g t c d1))
                                                                    with
                                                                    | 
                                                                    (comp_res_typing,
                                                                    uu___2,
                                                                    f) ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (x, g',
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Syntax_Base.comp_u
                                                                    c),
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c), ())),
                                                                    (Prims.Mkdtuple2
                                                                    (ctxt',
                                                                    ())),
                                                                    (k_elab_equiv
                                                                    g g'
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    Pulse_Syntax_Base.tm_emp
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c))
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt'
                                                                    Pulse_Syntax_Base.tm_emp)
                                                                    ctxt' k
                                                                    () ()))))))
                                                      uu___1))) uu___1)))
                                uu___1))) uu___)