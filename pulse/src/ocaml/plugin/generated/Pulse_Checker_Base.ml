open Prims
let (debug :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun f ->
           if
             Pulse_RuntimeUtils.debug_at_level (Pulse_Typing_Env.fstar_env g)
               "pulse.checker"
           then
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                              (Prims.of_int (32)) (Prims.of_int (12))
                              (Prims.of_int (32)) (Prims.of_int (17)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                              (Prims.of_int (32)) (Prims.of_int (4))
                              (Prims.of_int (32)) (Prims.of_int (17)))))
                     (Obj.magic (f ()))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic (FStar_Tactics_V2_Builtins.print uu___))
                          uu___)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
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
                   (Prims.of_int (35)) (Prims.of_int (39))
                   (Prims.of_int (35)) (Prims.of_int (83)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                   (Prims.of_int (35)) (Prims.of_int (86))
                   (Prims.of_int (50)) (Prims.of_int (21)))))
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
                              (Prims.of_int (36)) (Prims.of_int (24))
                              (Prims.of_int (38)) (Prims.of_int (40)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                              (Prims.of_int (39)) (Prims.of_int (4))
                              (Prims.of_int (50)) (Prims.of_int (21)))))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           fun ss ->
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (37))
                                        (Prims.of_int (18))
                                        (Prims.of_int (37))
                                        (Prims.of_int (102)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (36))
                                        (Prims.of_int (24))
                                        (Prims.of_int (38))
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
                                         (Prims.of_int (40))
                                         (Prims.of_int (36))
                                         (Prims.of_int (40))
                                         (Prims.of_int (71)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Base.fst"
                                         (Prims.of_int (41))
                                         (Prims.of_int (2))
                                         (Prims.of_int (50))
                                         (Prims.of_int (21)))))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      fun ts ->
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (40))
                                                   (Prims.of_int (50))
                                                   (Prims.of_int (40))
                                                   (Prims.of_int (71)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (40))
                                                   (Prims.of_int (36))
                                                   (Prims.of_int (40))
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
                                                    (Prims.of_int (50))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (50))
                                                    (Prims.of_int (21)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Base.fst"
                                                    (Prims.of_int (41))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (50))
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
                                                               (Prims.of_int (41))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (50))
                                                               (Prims.of_int (21)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Base.fst"
                                                               (Prims.of_int (41))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (50))
                                                               (Prims.of_int (21)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (23)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (50))
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
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
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
                     (Prims.of_int (64)) (Prims.of_int (10))
                     (Prims.of_int (64)) (Prims.of_int (17)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                     (Prims.of_int (64)) (Prims.of_int (20))
                     (Prims.of_int (80)) (Prims.of_int (72)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> Pulse_Typing_Env.fresh g))
            (fun uu___ ->
               (fun x ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                                (Prims.of_int (66)) (Prims.of_int (6))
                                (Prims.of_int (68)) (Prims.of_int (19)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                                (Prims.of_int (69)) (Prims.of_int (4))
                                (Prims.of_int (80)) (Prims.of_int (72)))))
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
                                           (Prims.of_int (70))
                                           (Prims.of_int (18))
                                           (Prims.of_int (70))
                                           (Prims.of_int (56)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Checker.Base.fst"
                                           (Prims.of_int (69))
                                           (Prims.of_int (4))
                                           (Prims.of_int (80))
                                           (Prims.of_int (72)))))
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
                                                          (Prims.of_int (71))
                                                          (Prims.of_int (27))
                                                          (Prims.of_int (71))
                                                          (Prims.of_int (53)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Base.fst"
                                                          (Prims.of_int (70))
                                                          (Prims.of_int (59))
                                                          (Prims.of_int (80))
                                                          (Prims.of_int (72)))))
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
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (119)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (72)))))
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
                                                                    Pulse_Typing.x
                                                                    = x;
                                                                    Pulse_Typing.post_typing_src
                                                                    = ();
                                                                    Pulse_Typing.post_typing
                                                                    = ()
                                                                    }))))
                                                      uu___2))) uu___)))
                            uu___))) uu___)
let (post_hint_from_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit) Pulse_Typing_Metatheory_Base.comp_typing_u ->
        unit Pulse_Typing.post_hint_for_env)
  =
  fun g ->
    fun c ->
      fun ct ->
        let st_comp_typing =
          Pulse_Typing_Metatheory_Base.comp_typing_inversion g c ct in
        let uu___ =
          Pulse_Typing_Metatheory_Base.st_comp_typing_inversion g
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
                Pulse_Typing.x = x;
                Pulse_Typing.post_typing_src = ();
                Pulse_Typing.post_typing = ()
              } in
            p
let (extend_post_hint :
  Pulse_Typing_Env.env ->
    unit Pulse_Typing.post_hint_for_env ->
      Pulse_Syntax_Base.var ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            unit ->
              (unit Pulse_Typing.post_hint_for_env, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun p ->
                   fun x ->
                     fun tx ->
                       fun conjunct ->
                         fun conjunct_typing ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   {
                                     Pulse_Typing.g =
                                       (Pulse_Typing_Env.push_binding g x
                                          Pulse_Syntax_Base.ppname_default tx);
                                     Pulse_Typing.ctag_hint =
                                       (p.Pulse_Typing.ctag_hint);
                                     Pulse_Typing.ret_ty =
                                       (p.Pulse_Typing.ret_ty);
                                     Pulse_Typing.u = (p.Pulse_Typing.u);
                                     Pulse_Typing.ty_typing = ();
                                     Pulse_Typing.post =
                                       (Pulse_Syntax_Base.tm_star
                                          p.Pulse_Typing.post conjunct);
                                     Pulse_Typing.x =
                                       (Pulse_Typing_Env.fresh
                                          (Pulse_Typing_Env.push_binding g x
                                             Pulse_Syntax_Base.ppname_default
                                             tx));
                                     Pulse_Typing.post_typing_src = ();
                                     Pulse_Typing.post_typing = ()
                                   }))) uu___5 uu___4 uu___3 uu___2 uu___1
                uu___
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
                                 (Prims.of_int (144)) (Prims.of_int (39))
                                 (Prims.of_int (144)) (Prims.of_int (57)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                                 (Prims.of_int (144)) (Prims.of_int (26))
                                 (Prims.of_int (144)) (Prims.of_int (57)))))
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
let (st_equiv_trans :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.comp ->
          (unit, unit, unit) Pulse_Typing.st_equiv ->
            (unit, unit, unit) Pulse_Typing.st_equiv ->
              (unit, unit, unit) Pulse_Typing.st_equiv
                FStar_Pervasives_Native.option)
  =
  fun g ->
    fun c0 ->
      fun c1 ->
        fun c2 ->
          fun d01 ->
            fun d12 ->
              match d01 with
              | Pulse_Typing.ST_VPropEquiv
                  (_f, _c0, _c1, x, c0_pre_typing, c0_res_typing,
                   c0_post_typing, eq_res_01, eq_pre_01, eq_post_01)
                  ->
                  let uu___ = d12 in
                  (match uu___ with
                   | Pulse_Typing.ST_VPropEquiv
                       (_f1, _c11, _c2, y, c1_pre_typing, c1_res_typing,
                        c1_post_typing, eq_res_12, eq_pre_12, eq_post_12)
                       ->
                       if
                         (x = y) &&
                           (Pulse_Syntax_Base.eq_tm
                              (Pulse_Syntax_Base.comp_res c0)
                              (Pulse_Syntax_Base.comp_res c1))
                       then
                         FStar_Pervasives_Native.Some
                           (Pulse_Typing.ST_VPropEquiv
                              (g, c0, c2, x, (), (), (),
                                (FStar_Reflection_Typing.Rel_trans
                                   ((Pulse_Typing.elab_env _f),
                                     (Pulse_Elaborate_Pure.elab_term
                                        (Pulse_Syntax_Base.comp_res _c0)),
                                     (Pulse_Elaborate_Pure.elab_term
                                        (Pulse_Syntax_Base.comp_res _c1)),
                                     (Pulse_Elaborate_Pure.elab_term
                                        (Pulse_Syntax_Base.comp_res _c2)),
                                     FStar_Reflection_Typing.R_Eq, eq_res_01,
                                     eq_res_12)), (), ()))
                       else FStar_Pervasives_Native.None)
              | Pulse_Typing.ST_TotEquiv (g1, t1, t2, u, typing, eq) ->
                  let uu___ = d12 in
                  (match uu___ with
                   | Pulse_Typing.ST_TotEquiv
                       (_g, _t1, t3, uu___1, uu___2, eq') ->
                       FStar_Pervasives_Native.Some
                         (Pulse_Typing.ST_TotEquiv (g1, t1, t3, u, (), ())))
let (t_equiv :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.comp ->
            (unit, unit, unit) Pulse_Typing.st_equiv ->
              (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun st ->
      fun c ->
        fun d ->
          fun c' ->
            fun eq ->
              match d with
              | Pulse_Typing.T_Equiv (uu___, uu___1, uu___2, uu___3, d0, eq')
                  ->
                  (match st_equiv_trans uu___ uu___2 uu___3 c' eq' eq with
                   | FStar_Pervasives_Native.None ->
                       Pulse_Typing.T_Equiv (g, st, c, c', d, eq)
                   | FStar_Pervasives_Native.Some eq'' ->
                       Pulse_Typing.T_Equiv
                         (uu___, uu___1, uu___2, c', d0, eq''))
              | uu___ -> Pulse_Typing.T_Equiv (g, st, c, c', d, eq)
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
              if Pulse_Syntax_Base.eq_tm post (Pulse_Syntax_Base.comp_post c)
              then d
              else
                (let c' = comp_st_with_post c post in
                 let uu___1 =
                   Pulse_Typing_Metatheory_Base.st_comp_typing_inversion g
                     (Pulse_Syntax_Base.st_comp_of_comp c)
                     (Pulse_Typing_Metatheory_Base.comp_typing_inversion g c
                        (Pulse_Typing_Metatheory_Base.st_typing_correctness g
                           t c d)) in
                 match uu___1 with
                 | FStar_Pervasives.Mkdtuple4
                     (u_of, pre_typing, x, post_typing) ->
                     let st_equiv =
                       Pulse_Typing.ST_VPropEquiv
                         (g, c, c', x, (), (), (),
                           (FStar_Reflection_Typing.Rel_refl
                              ((Pulse_Typing.elab_env g),
                                (Pulse_Elaborate_Pure.elab_term
                                   (Pulse_Syntax_Base.comp_res c)),
                                FStar_Reflection_Typing.R_Eq)), (), ()) in
                     t_equiv g t c d c' st_equiv)
let (simplify_post :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.term -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t -> fun c -> fun d -> fun post -> st_equiv_post g t c d post ()

let (comp_with_pre :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp)
  =
  fun c ->
    fun pre ->
      match c with
      | Pulse_Syntax_Base.C_ST st ->
          Pulse_Syntax_Base.C_ST
            {
              Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
              Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
              Pulse_Syntax_Base.pre = pre;
              Pulse_Syntax_Base.post = (st.Pulse_Syntax_Base.post)
            }
      | Pulse_Syntax_Base.C_STGhost (i, st) ->
          Pulse_Syntax_Base.C_STGhost
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = pre;
                Pulse_Syntax_Base.post = (st.Pulse_Syntax_Base.post)
              })
      | Pulse_Syntax_Base.C_STAtomic (i, st) ->
          Pulse_Syntax_Base.C_STAtomic
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = pre;
                Pulse_Syntax_Base.post = (st.Pulse_Syntax_Base.post)
              })
let (st_equiv_pre :
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
          fun pre ->
            fun veq ->
              if Pulse_Syntax_Base.eq_tm pre (Pulse_Syntax_Base.comp_pre c)
              then d
              else
                (let c' = comp_with_pre c pre in
                 let uu___1 =
                   Pulse_Typing_Metatheory_Base.st_comp_typing_inversion g
                     (Pulse_Syntax_Base.st_comp_of_comp c)
                     (Pulse_Typing_Metatheory_Base.comp_typing_inversion g c
                        (Pulse_Typing_Metatheory_Base.st_typing_correctness g
                           t c d)) in
                 match uu___1 with
                 | FStar_Pervasives.Mkdtuple4
                     (u_of, pre_typing, x, post_typing) ->
                     let st_equiv =
                       Pulse_Typing.ST_VPropEquiv
                         (g, c, c', x, (), (), (),
                           (FStar_Reflection_Typing.Rel_refl
                              ((Pulse_Typing.elab_env g),
                                (Pulse_Elaborate_Pure.elab_term
                                   (Pulse_Syntax_Base.comp_res c)),
                                FStar_Reflection_Typing.R_Eq)), (), ()) in
                     t_equiv g t c d c' st_equiv)
let (k_elab_equiv_continuation :
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
                               (Prims.of_int (253)) (Prims.of_int (28))
                               (Prims.of_int (253)) (Prims.of_int (31)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                               (Prims.of_int (252)) (Prims.of_int (22))
                               (Prims.of_int (257)) (Prims.of_int (34)))))
                      (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> res))
                      (fun uu___ ->
                         (fun uu___ ->
                            match uu___ with
                            | FStar_Pervasives.Mkdtuple3 (st, c, st_d) ->
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Base.fst"
                                              (Prims.of_int (254))
                                              (Prims.of_int (35))
                                              (Prims.of_int (254))
                                              (Prims.of_int (39)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Base.fst"
                                              (Prims.of_int (255))
                                              (Prims.of_int (33))
                                              (Prims.of_int (257))
                                              (Prims.of_int (34)))))
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 -> st_d))
                                     (fun uu___1 ->
                                        (fun st_d1 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Base.fst"
                                                         (Prims.of_int (256))
                                                         (Prims.of_int (58))
                                                         (Prims.of_int (256))
                                                         (Prims.of_int (94)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Base.fst"
                                                         (Prims.of_int (257))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (257))
                                                         (Prims.of_int (34)))))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___1 ->
                                                      st_equiv_pre g2 st c
                                                        st_d1 ctxt1 ()))
                                                (fun uu___1 ->
                                                   (fun st_d' ->
                                                      Obj.magic
                                                        (k post_hint
                                                           (FStar_Pervasives.Mkdtuple3
                                                              (st,
                                                                (comp_with_pre
                                                                   c ctxt1),
                                                                st_d'))))
                                                     uu___1))) uu___1)))
                           uu___)

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
                               (Prims.of_int (273)) (Prims.of_int (60))
                               (Prims.of_int (275)) (Prims.of_int (31)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                               (Prims.of_int (276)) (Prims.of_int (4))
                               (Prims.of_int (280)) (Prims.of_int (35)))))
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
                                          (Prims.of_int (277))
                                          (Prims.of_int (12))
                                          (Prims.of_int (277))
                                          (Prims.of_int (27)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Base.fst"
                                          (Prims.of_int (277))
                                          (Prims.of_int (30))
                                          (Prims.of_int (280))
                                          (Prims.of_int (35)))))
                                 (Obj.magic (k post_hint res))
                                 (fun res1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ ->
                                         match res1 with
                                         | FStar_Pervasives.Mkdtuple3
                                             (st, c, st_d) ->
                                             FStar_Pervasives.Mkdtuple3
                                               (st, (comp_with_pre c ctxt2),
                                                 (st_equiv_pre g1 st c st_d
                                                    ctxt2 ())))))) uu___)
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
                      k_elab_equiv_continuation g1 g2 ctxt1 ctxt2 ctxt2' k () in
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
              Pulse_Syntax_Base.nvar ->
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
                                           (match Pulse_Typing_Metatheory_Base.st_comp_typing_inversion
                                                    g
                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                       c11)
                                                    (Pulse_Typing_Metatheory_Base.comp_typing_inversion
                                                       g c11
                                                       (Pulse_Typing_Metatheory_Base.st_typing_correctness
                                                          g e1 c11 e1_typing1))
                                            with
                                            | FStar_Pervasives.Mkdtuple4
                                                (u_of_1, pre_typing, uu___1,
                                                 uu___2)
                                                ->
                                                (match x with
                                                 | (ppname, x1) ->
                                                     (fun post_hint ->
                                                        fun res ->
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (37)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (5)))))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___3 ->
                                                                  res))
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
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (357))
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
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    e2 x1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    e2_closed
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    x1
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c2))
                                                                    then
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x1
                                                                    ppname
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
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Combinators.bind_res_and_post_typing
                                                                    g
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2) x1
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
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (356))
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
                                                                    (ppname,
                                                                    x1)
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
                                                                 uu___3)))))))
                  uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (continuation_elaborator_with_let :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.term ->
          FStar_TypeChecker_Core.tot_or_ghost ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.binder ->
                unit ->
                  Pulse_Syntax_Base.nvar ->
                    ((unit, unit, unit, unit) continuation_elaborator, 
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___8 ->
    fun uu___7 ->
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
                             fun eff1 ->
                               fun t1 ->
                                 fun b ->
                                   fun e1_typing ->
                                     fun x ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___ ->
                                               fun post_hint ->
                                                 fun uu___1 ->
                                                   match uu___1 with
                                                   | FStar_Pervasives.Mkdtuple3
                                                       (e2, c2, d2) ->
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Base.fst"
                                                                  (Prims.of_int (378))
                                                                  (Prims.of_int (2))
                                                                  (Prims.of_int (383))
                                                                  (Prims.of_int (34)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Base.fst"
                                                                  (Prims.of_int (383))
                                                                  (Prims.of_int (35))
                                                                  (Prims.of_int (426))
                                                                  (Prims.of_int (15)))))
                                                         (if
                                                            (eff1 =
                                                               FStar_TypeChecker_Core.E_Ghost)
                                                              &&
                                                              (Prims.op_Negation
                                                                 (Pulse_Syntax_Base.uu___is_C_STGhost
                                                                    c2))
                                                          then
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (34)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (34)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    c2))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    e1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Cannot bind ghost expression "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " with "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    " computation")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e1.Pulse_Syntax_Base.range1))
                                                                    uu___2))
                                                                    uu___2)))
                                                          else
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    ()))))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (19)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (15)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    x))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (ppname,
                                                                    x1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (15)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    e2 x1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    e2_closed
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (15)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.wr
                                                                    c2
                                                                    (Pulse_Syntax_Base.Tm_TotBind
                                                                    {
                                                                    Pulse_Syntax_Base.binder1
                                                                    = b;
                                                                    Pulse_Syntax_Base.head2
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body2
                                                                    =
                                                                    e2_closed
                                                                    })))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun e ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (15)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.open_comp_with
                                                                    (Pulse_Syntax_Naming.close_comp
                                                                    c2 x1) e1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun c ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (15)))))
                                                                    (if
                                                                    eff1 =
                                                                    FStar_TypeChecker_Core.E_Total
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.T_TotBind
                                                                    (g, e1,
                                                                    e2_closed,
                                                                    t1, c2,
                                                                    b, x1,
                                                                    (), d2))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.is_non_informative
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g x1
                                                                    ppname t1)
                                                                    c2))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    token ->
                                                                    match token
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    c2))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "Impossible! Non-informative for "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    " returned None")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    uu___5))
                                                                    uu___5)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    token1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_GhostBind
                                                                    (g, e1,
                                                                    e2_closed,
                                                                    t1, c2,
                                                                    b, x1,
                                                                    (), d2,
                                                                    ())))))
                                                                    uu___5))))
                                                                    (fun d ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e, c, d)))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                              uu___2))))
                      uu___8 uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1
                      uu___
let (st_comp_typing_with_post_hint :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit) Pulse_Typing.st_comp_typing)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun post_hint ->
          fun c ->
            let st = Pulse_Syntax_Base.st_comp_of_comp c in
            let uu___ = post_hint in
            match uu___ with
            | FStar_Pervasives_Native.Some ph ->
                let x = Pulse_Typing_Env.fresh g in
                Pulse_Typing.STC (g, st, x, (), (), ())
let (continuation_elaborator_with_bind_fn :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp ->
            Pulse_Syntax_Base.binder ->
              (unit, unit, unit) Pulse_Typing.st_typing ->
                Pulse_Syntax_Base.nvar ->
                  ((unit, unit, unit, unit) continuation_elaborator, 
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___7 ->
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
                           fun c1 ->
                             fun b ->
                               fun e1_typing ->
                                 fun x ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___ ->
                                           fun post_hint ->
                                             fun uu___1 ->
                                               match uu___1 with
                                               | FStar_Pervasives.Mkdtuple3
                                                   (e2, c2, d2) ->
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Base.fst"
                                                              (Prims.of_int (491))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (491))
                                                              (Prims.of_int (77)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Base.fst"
                                                              (Prims.of_int (491))
                                                              (Prims.of_int (78))
                                                              (Prims.of_int (516))
                                                              (Prims.of_int (18)))))
                                                     (if
                                                        FStar_Pervasives_Native.uu___is_None
                                                          post_hint
                                                      then
                                                        FStar_Tactics_V2_Derived.fail
                                                          "bind_fn: expects the post_hint to be set"
                                                      else
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 -> ()))
                                                     (fun uu___2 ->
                                                        (fun uu___2 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (21)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (18)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    x))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (ppname,
                                                                    x1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    e2 x1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    e2_closed
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing.wr
                                                                    c2
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    =
                                                                    e2_closed
                                                                    })))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun e ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Metatheory_Base.st_typing_correctness_ctot
                                                                    g e1 c1
                                                                    e1_typing))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u,
                                                                    c1_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (18)))))
                                                                    (match c2
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_ST
                                                                    st ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.CT_ST
                                                                    (g,
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2),
                                                                    (st_comp_typing_with_post_hint
                                                                    g ctxt ()
                                                                    post_hint
                                                                    c2)))))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (i, st)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    st_comp_typing_with_post_hint
                                                                    g ctxt ()
                                                                    post_hint
                                                                    c2))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun stc
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.core_check_term
                                                                    g i
                                                                    FStar_TypeChecker_Core.E_Total
                                                                    Pulse_Syntax_Base.tm_inames))
                                                                    (fun
                                                                    i_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.CT_STAtomic
                                                                    (g, i,
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2), (),
                                                                    stc)))))
                                                                    uu___5)))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (i, st)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (509))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (509))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (509))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    st_comp_typing_with_post_hint
                                                                    g ctxt ()
                                                                    post_hint
                                                                    c2))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun stc
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.core_check_term
                                                                    g i
                                                                    FStar_TypeChecker_Core.E_Total
                                                                    Pulse_Syntax_Base.tm_inames))
                                                                    (fun
                                                                    i_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.CT_STGhost
                                                                    (g, i,
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2), (),
                                                                    stc)))))
                                                                    uu___5))))
                                                                    (fun
                                                                    c2_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e, c2,
                                                                    (Pulse_Typing.T_BindFn
                                                                    (g, e1,
                                                                    e2_closed,
                                                                    c1, c2,
                                                                    b, x1,
                                                                    e1_typing,
                                                                    (), (),
                                                                    d2,
                                                                    c2_typing)))))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                          uu___2)))) uu___7
                    uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
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
          Pulse_Syntax_Base.ppname ->
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
                         (Prims.of_int (545)) (Prims.of_int (8))
                         (Prims.of_int (545)) (Prims.of_int (52)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                         (Prims.of_int (547)) (Prims.of_int (4))
                         (Prims.of_int (562)) (Prims.of_int (40)))))
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
                                        (Prims.of_int (549))
                                        (Prims.of_int (16))
                                        (Prims.of_int (549))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (550))
                                        (Prims.of_int (6))
                                        (Prims.of_int (550))
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
                                        (Prims.of_int (552))
                                        (Prims.of_int (16))
                                        (Prims.of_int (552))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (552))
                                        (Prims.of_int (42))
                                        (Prims.of_int (556))
                                        (Prims.of_int (41)))))
                               (Obj.magic (intro_st_comp_typing st))
                               (fun uu___ ->
                                  (fun stc ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (553))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (553))
                                                   (Prims.of_int (64)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (552))
                                                   (Prims.of_int (42))
                                                   (Prims.of_int (556))
                                                   (Prims.of_int (41)))))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.core_compute_tot_term_type
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
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (87)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (87)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (555))
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
                                        (Prims.of_int (558))
                                        (Prims.of_int (16))
                                        (Prims.of_int (558))
                                        (Prims.of_int (39)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (558))
                                        (Prims.of_int (42))
                                        (Prims.of_int (562))
                                        (Prims.of_int (40)))))
                               (Obj.magic (intro_st_comp_typing st))
                               (fun uu___ ->
                                  (fun stc ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (559))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (559))
                                                   (Prims.of_int (64)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Base.fst"
                                                   (Prims.of_int (558))
                                                   (Prims.of_int (42))
                                                   (Prims.of_int (562))
                                                   (Prims.of_int (40)))))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.core_compute_tot_term_type
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
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (87)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (87)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (561))
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
      Pulse_Syntax_Base.ppname ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.vprop ->
              unit ->
                unit Pulse_Typing.post_hint_opt ->
                  (unit, unit, unit)
                    Pulse_Typing_Combinators.st_typing_in_ctxt)
  =
  fun g ->
    fun y ->
      fun y_ppname ->
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
                        | FStar_Pervasives_Native.None ->
                            Pulse_Syntax_Base.STT
                        | FStar_Pervasives_Native.Some ctag1 -> ctag1 in
                      let y_tm =
                        Pulse_Syntax_Pure.tm_var
                          {
                            Pulse_Syntax_Base.nm_index = y;
                            Pulse_Syntax_Base.nm_ppname = y_ppname
                          } in
                      let d =
                        Pulse_Typing.T_Return
                          (g, ctag, false, u, ty, y_tm,
                            (post_hint.Pulse_Typing.post), x, (), (), ()) in
                      let t =
                        Pulse_Typing.wtag (FStar_Pervasives_Native.Some ctag)
                          (Pulse_Syntax_Base.Tm_Return
                             {
                               Pulse_Syntax_Base.ctag = ctag;
                               Pulse_Syntax_Base.insert_eq = false;
                               Pulse_Syntax_Base.term = y_tm
                             }) in
                      let c =
                        Pulse_Typing.comp_return ctag false u ty y_tm
                          post_hint.Pulse_Typing.post x in
                      let d1 = d in FStar_Pervasives.Mkdtuple3 (t, c, d1)
let (match_comp_res_with_post_hint :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          unit Pulse_Typing.post_hint_opt ->
            ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
               (unit, unit, unit) Pulse_Typing.st_typing)
               FStar_Pervasives.dtuple3,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun g ->
               fun t ->
                 fun c ->
                   fun d ->
                     fun post_hint ->
                       match post_hint with
                       | FStar_Pervasives_Native.None ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      FStar_Pervasives.Mkdtuple3 (t, c, d))))
                       | FStar_Pervasives_Native.Some
                           { Pulse_Typing.g = uu___;
                             Pulse_Typing.ctag_hint = uu___1;
                             Pulse_Typing.ret_ty = ret_ty;
                             Pulse_Typing.u = uu___2;
                             Pulse_Typing.ty_typing = uu___3;
                             Pulse_Typing.post = uu___4;
                             Pulse_Typing.x = uu___5;
                             Pulse_Typing.post_typing_src = uu___6;
                             Pulse_Typing.post_typing = uu___7;_}
                           ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Base.fst"
                                            (Prims.of_int (607))
                                            (Prims.of_int (15))
                                            (Prims.of_int (607))
                                            (Prims.of_int (25)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Base.fst"
                                            (Prims.of_int (608))
                                            (Prims.of_int (4))
                                            (Prims.of_int (629))
                                            (Prims.of_int (51)))))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___8 ->
                                         Pulse_Syntax_Base.comp_res c))
                                   (fun uu___8 ->
                                      (fun cres ->
                                         if
                                           Pulse_Syntax_Base.eq_tm cres
                                             ret_ty
                                         then
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___8 ->
                                                      FStar_Pervasives.Mkdtuple3
                                                        (t, c, d))))
                                         else
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Base.fst"
                                                            (Prims.of_int (610))
                                                            (Prims.of_int (15))
                                                            (Prims.of_int (610))
                                                            (Prims.of_int (59)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Base.fst"
                                                            (Prims.of_int (610))
                                                            (Prims.of_int (9))
                                                            (Prims.of_int (629))
                                                            (Prims.of_int (51)))))
                                                   (Obj.magic
                                                      (Pulse_Checker_Pure.check_equiv
                                                         g cres ret_ty))
                                                   (fun uu___9 ->
                                                      (fun uu___9 ->
                                                         match uu___9 with
                                                         | FStar_Pervasives_Native.None
                                                             ->
                                                             Obj.magic
                                                               (Obj.repr
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (615))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (612))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (615))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (615))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (615))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (615))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ret_ty))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (615))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (615))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (614))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (614))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    cres))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Could not prove equiv for computed type "
                                                                    (Prims.strcat
                                                                    uu___11
                                                                    " and expected type "))
                                                                    (Prims.strcat
                                                                    x "")))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    uu___11
                                                                    uu___10))))
                                                                    uu___10)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range2))
                                                                    uu___10))
                                                                    uu___10)))
                                                         | FStar_Pervasives_Native.Some
                                                             tok ->
                                                             Obj.magic
                                                               (Obj.repr
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match 
                                                                    Pulse_Typing_Metatheory_Base.st_comp_typing_inversion
                                                                    g
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c)
                                                                    (Pulse_Typing_Metatheory_Base.comp_typing_inversion
                                                                    g c
                                                                    (Pulse_Typing_Metatheory_Base.st_typing_correctness
                                                                    g t c d))
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (cres_typing,
                                                                    cpre_typing,
                                                                    x,
                                                                    cpost_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t,
                                                                    (Pulse_Syntax_Base.with_st_comp
                                                                    c
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    c).Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.res
                                                                    = ret_ty;
                                                                    Pulse_Syntax_Base.pre
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    c).Pulse_Syntax_Base.pre);
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    c).Pulse_Syntax_Base.post)
                                                                    }),
                                                                    (Pulse_Typing.T_Equiv
                                                                    (g, t, c,
                                                                    (Pulse_Syntax_Base.with_st_comp
                                                                    c
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    c).Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.res
                                                                    = ret_ty;
                                                                    Pulse_Syntax_Base.pre
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    c).Pulse_Syntax_Base.pre);
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    c).Pulse_Syntax_Base.post)
                                                                    }), d,
                                                                    (Pulse_Typing.ST_VPropEquiv
                                                                    (g, c,
                                                                    (Pulse_Syntax_Base.with_st_comp
                                                                    c
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    c).Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.res
                                                                    = ret_ty;
                                                                    Pulse_Syntax_Base.pre
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    c).Pulse_Syntax_Base.pre);
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    c).Pulse_Syntax_Base.post)
                                                                    }), x,
                                                                    (), (),
                                                                    (),
                                                                    (FStar_Reflection_Typing.Rel_eq_token
                                                                    ((Pulse_Typing.elab_env
                                                                    g),
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    cres),
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    ret_ty),
                                                                    ())), (),
                                                                    ())))))))))
                                                        uu___9)))) uu___8))))
              uu___4 uu___3 uu___2 uu___1 uu___
let (apply_checker_result_k :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit Pulse_Typing.post_hint_for_env ->
        (unit, unit, unit) checker_result_t ->
          Pulse_Syntax_Base.ppname ->
            ((unit, unit, unit) Pulse_Typing_Combinators.st_typing_in_ctxt,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun post_hint ->
        fun r ->
          fun res_ppname ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                       (Prims.of_int (637)) (Prims.of_int (64))
                       (Prims.of_int (637)) (Prims.of_int (65)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                       (Prims.of_int (634)) (Prims.of_int (55))
                       (Prims.of_int (644)) (Prims.of_int (22)))))
              (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> r))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | FStar_Pervasives.Mkdtuple5
                        (y, g1, FStar_Pervasives.Mkdtuple3
                         (u_ty, ty_y, d_ty_y), Prims.Mkdtuple2
                         (pre', uu___1), k)
                        ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Base.fst"
                                      (Prims.of_int (639))
                                      (Prims.of_int (29))
                                      (Prims.of_int (639))
                                      (Prims.of_int (70)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Base.fst"
                                      (Prims.of_int (637))
                                      (Prims.of_int (68))
                                      (Prims.of_int (644))
                                      (Prims.of_int (22)))))
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
                                                     (Prims.of_int (642))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (642))
                                                     (Prims.of_int (75)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Base.fst"
                                                     (Prims.of_int (644))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (644))
                                                     (Prims.of_int (22)))))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  return_in_ctxt g1 y
                                                    res_ppname u_ty_y ty_y
                                                    pre' ()
                                                    (FStar_Pervasives_Native.Some
                                                       post_hint)))
                                            (fun uu___3 ->
                                               (fun d ->
                                                  Obj.magic
                                                    (k
                                                       (FStar_Pervasives_Native.Some
                                                          post_hint) d))
                                                 uu___3))) uu___2))) uu___)
let (checker_result_for_st_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit Pulse_Typing.post_hint_opt ->
        (unit, unit, unit) Pulse_Typing_Combinators.st_typing_in_ctxt ->
          Pulse_Syntax_Base.ppname ->
            ((unit, unit, unit) checker_result_t, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun post_hint ->
        fun d ->
          fun ppname ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                       (Prims.of_int (652)) (Prims.of_int (22))
                       (Prims.of_int (652)) (Prims.of_int (23)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                       (Prims.of_int (650)) (Prims.of_int (47))
                       (Prims.of_int (682)) (Prims.of_int (66)))))
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
                                      (Prims.of_int (654))
                                      (Prims.of_int (10))
                                      (Prims.of_int (654))
                                      (Prims.of_int (17)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Base.fst"
                                      (Prims.of_int (654))
                                      (Prims.of_int (20))
                                      (Prims.of_int (682))
                                      (Prims.of_int (66)))))
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
                                                 (Prims.of_int (656))
                                                 (Prims.of_int (11))
                                                 (Prims.of_int (656))
                                                 (Prims.of_int (47)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Base.fst"
                                                 (Prims.of_int (656))
                                                 (Prims.of_int (50))
                                                 (Prims.of_int (682))
                                                 (Prims.of_int (66)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              Pulse_Typing_Env.push_binding g
                                                x ppname
                                                (Pulse_Syntax_Base.comp_res c)))
                                        (fun uu___1 ->
                                           (fun g' ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Base.fst"
                                                            (Prims.of_int (657))
                                                            (Prims.of_int (14))
                                                            (Prims.of_int (657))
                                                            (Prims.of_int (52)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Base.fst"
                                                            (Prims.of_int (657))
                                                            (Prims.of_int (55))
                                                            (Prims.of_int (682))
                                                            (Prims.of_int (66)))))
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         Pulse_Syntax_Naming.open_term_nv
                                                           (Pulse_Syntax_Base.comp_post
                                                              c) (ppname, x)))
                                                   (fun uu___1 ->
                                                      (fun ctxt' ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (72)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (682))
                                                                    (Prims.of_int (66)))))
                                                              (Obj.magic
                                                                 (continuation_elaborator_with_bind
                                                                    g
                                                                    Pulse_Syntax_Base.tm_emp
                                                                    c t d1 ()
                                                                    (ppname,
                                                                    x)))
                                                              (fun k ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___1 ->
                                                                    match 
                                                                    Pulse_Typing_Metatheory_Base.st_comp_typing_inversion_cofinite
                                                                    g
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c)
                                                                    (Pulse_Typing_Metatheory_Base.comp_typing_inversion
                                                                    g c
                                                                    (Pulse_Typing_Metatheory_Base.st_typing_correctness
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
let (readback_comp_res_as_comp :
  FStar_Tactics_NamedView.comp ->
    Pulse_Syntax_Base.comp FStar_Pervasives_Native.option)
  =
  fun c ->
    match c with
    | FStar_Reflection_V2_Data.C_Total t ->
        (match Pulse_Readback.readback_comp t with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some c1 -> FStar_Pervasives_Native.Some c1)
    | uu___ -> FStar_Pervasives_Native.None
let rec (is_stateful_arrow :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp FStar_Pervasives_Native.option ->
      FStar_Reflection_V2_Data.argv Prims.list ->
        FStar_Reflection_V2_Data.argv Prims.list ->
          ((FStar_Reflection_V2_Data.argv Prims.list *
             FStar_Reflection_V2_Data.argv) FStar_Pervasives_Native.option,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun c ->
               fun args ->
                 fun out ->
                   match c with
                   | FStar_Pervasives_Native.None ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> FStar_Pervasives_Native.None)))
                   | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.C_ST
                       uu___) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 ->
                                  match (args, out) with
                                  | ([], hd::tl) ->
                                      FStar_Pervasives_Native.Some
                                        ((FStar_List_Tot_Base.rev tl), hd)
                                  | uu___2 -> FStar_Pervasives_Native.None)))
                   | FStar_Pervasives_Native.Some
                       (Pulse_Syntax_Base.C_STGhost (uu___, uu___1)) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 ->
                                  match (args, out) with
                                  | ([], hd::tl) ->
                                      FStar_Pervasives_Native.Some
                                        ((FStar_List_Tot_Base.rev tl), hd)
                                  | uu___3 -> FStar_Pervasives_Native.None)))
                   | FStar_Pervasives_Native.Some
                       (Pulse_Syntax_Base.C_STAtomic (uu___, uu___1)) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 ->
                                  match (args, out) with
                                  | ([], hd::tl) ->
                                      FStar_Pervasives_Native.Some
                                        ((FStar_List_Tot_Base.rev tl), hd)
                                  | uu___3 -> FStar_Pervasives_Native.None)))
                   | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.C_Tot
                       c_res) ->
                       Obj.magic
                         (Obj.repr
                            (if
                               Prims.op_Negation
                                 (Pulse_Syntax_Base.uu___is_Tm_FStar
                                    c_res.Pulse_Syntax_Base.t)
                             then
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ ->
                                       FStar_Pervasives_Native.None))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Base.fst"
                                             (Prims.of_int (713))
                                             (Prims.of_int (29))
                                             (Prims.of_int (713))
                                             (Prims.of_int (36)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Base.fst"
                                             (Prims.of_int (712))
                                             (Prims.of_int (11))
                                             (Prims.of_int (750))
                                             (Prims.of_int (7)))))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 ->
                                          c_res.Pulse_Syntax_Base.t))
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          match uu___1 with
                                          | Pulse_Syntax_Base.Tm_FStar c_res1
                                              ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Base.fst"
                                                            (Prims.of_int (714))
                                                            (Prims.of_int (17))
                                                            (Prims.of_int (714))
                                                            (Prims.of_int (32)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Base.fst"
                                                            (Prims.of_int (715))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (749))
                                                            (Prims.of_int (19)))))
                                                   (Obj.magic
                                                      (FStar_Tactics_NamedView.inspect
                                                         c_res1))
                                                   (fun uu___2 ->
                                                      (fun ht ->
                                                         match ht with
                                                         | FStar_Tactics_NamedView.Tv_Arrow
                                                             (b, c1) ->
                                                             Obj.magic
                                                               (Obj.repr
                                                                  (match args
                                                                   with
                                                                   | 
                                                                   [] ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (719))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (719))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (723))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Reflection_V2_Derived.collect_arr_ln_bs
                                                                    c_res1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (bs, c2)
                                                                    ->
                                                                    if
                                                                    FStar_List_Tot_Base.for_all
                                                                    (fun b1
                                                                    ->
                                                                    FStar_Reflection_V2_Data.uu___is_Q_Implicit
                                                                    (FStar_Reflection_V2_Builtins.inspect_binder
                                                                    b1).FStar_Reflection_V2_Data.qual)
                                                                    bs
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (is_stateful_arrow
                                                                    g
                                                                    (readback_comp_res_as_comp
                                                                    (FStar_Reflection_V2_Builtins.inspect_comp
                                                                    c2)) []
                                                                    out))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___2))
                                                                   | 
                                                                   (arg,
                                                                    qual)::args'
                                                                    ->
                                                                    Obj.repr
                                                                    (match 
                                                                    ((b.FStar_Tactics_NamedView.qual),
                                                                    qual)
                                                                    with
                                                                    | 
                                                                    (FStar_Reflection_V2_Data.Q_Meta
                                                                    uu___2,
                                                                    FStar_Reflection_V2_Data.Q_Implicit)
                                                                    ->
                                                                    Obj.repr
                                                                    (is_stateful_arrow
                                                                    g
                                                                    (readback_comp_res_as_comp
                                                                    c1) args'
                                                                    ((arg,
                                                                    qual) ::
                                                                    out))
                                                                    | 
                                                                    (FStar_Reflection_V2_Data.Q_Implicit,
                                                                    FStar_Reflection_V2_Data.Q_Implicit)
                                                                    ->
                                                                    Obj.repr
                                                                    (is_stateful_arrow
                                                                    g
                                                                    (readback_comp_res_as_comp
                                                                    c1) args'
                                                                    ((arg,
                                                                    qual) ::
                                                                    out))
                                                                    | 
                                                                    (FStar_Reflection_V2_Data.Q_Explicit,
                                                                    FStar_Reflection_V2_Data.Q_Explicit)
                                                                    ->
                                                                    Obj.repr
                                                                    (is_stateful_arrow
                                                                    g
                                                                    (readback_comp_res_as_comp
                                                                    c1) args'
                                                                    ((arg,
                                                                    qual) ::
                                                                    out))
                                                                    | 
                                                                    (FStar_Reflection_V2_Data.Q_Meta
                                                                    uu___2,
                                                                    FStar_Reflection_V2_Data.Q_Explicit)
                                                                    ->
                                                                    Obj.repr
                                                                    (is_stateful_arrow
                                                                    g
                                                                    (readback_comp_res_as_comp
                                                                    c1) args
                                                                    out)
                                                                    | 
                                                                    (FStar_Reflection_V2_Data.Q_Implicit,
                                                                    FStar_Reflection_V2_Data.Q_Explicit)
                                                                    ->
                                                                    Obj.repr
                                                                    (is_stateful_arrow
                                                                    g
                                                                    (readback_comp_res_as_comp
                                                                    c1) args
                                                                    out)
                                                                    | 
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.None)))))
                                                         | uu___2 ->
                                                             Obj.magic
                                                               (Obj.repr
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_RuntimeUtils.whnf_lax
                                                                    (Pulse_Typing.elab_env
                                                                    g) c_res1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    c_res' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (743))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (749))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_NamedView.inspect
                                                                    c_res'))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun ht1
                                                                    ->
                                                                    if
                                                                    FStar_Tactics_NamedView.uu___is_Tv_Arrow
                                                                    ht1
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (746))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (746))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Base.fst"
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Base.tm_fstar
                                                                    c_res'
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    c_res')))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    c_res'1
                                                                    ->
                                                                    Obj.magic
                                                                    (is_stateful_arrow
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.C_Tot
                                                                    c_res'1))
                                                                    args out))
                                                                    uu___3)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___3)))
                                                                    uu___3))))
                                                        uu___2))) uu___1)))))
            uu___3 uu___2 uu___1 uu___
let (is_stateful_application :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (Pulse_Syntax_Base.st_term FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun e ->
           match e.Pulse_Syntax_Base.t with
           | Pulse_Syntax_Base.Tm_FStar host_term ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                                (Prims.of_int (758)) (Prims.of_int (23))
                                (Prims.of_int (758)) (Prims.of_int (49)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                                (Prims.of_int (757)) (Prims.of_int (28))
                                (Prims.of_int (781)) (Prims.of_int (5)))))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             FStar_Reflection_V2_Derived.collect_app_ln
                               host_term))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | (head, args) ->
                                 (match Pulse_RuntimeUtils.lax_check_term_with_unknown_universes
                                          (Pulse_Typing.elab_env g) head
                                  with
                                  | FStar_Pervasives_Native.None ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 ->
                                                 FStar_Pervasives_Native.None)))
                                  | FStar_Pervasives_Native.Some ht ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Base.fst"
                                                       (Prims.of_int (764))
                                                       (Prims.of_int (21))
                                                       (Prims.of_int (764))
                                                       (Prims.of_int (53)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Base.fst"
                                                       (Prims.of_int (765))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (780))
                                                       (Prims.of_int (21)))))
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    Pulse_Syntax_Base.tm_fstar
                                                      ht
                                                      (FStar_Reflection_V2_Builtins.range_of_term
                                                         ht)))
                                              (fun uu___1 ->
                                                 (fun head_t ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Base.fst"
                                                                  (Prims.of_int (765))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (765))
                                                                  (Prims.of_int (63)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Base.fst"
                                                                  (Prims.of_int (765))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (780))
                                                                  (Prims.of_int (21)))))
                                                         (Obj.magic
                                                            (is_stateful_arrow
                                                               g
                                                               (FStar_Pervasives_Native.Some
                                                                  (Pulse_Syntax_Base.C_Tot
                                                                    head_t))
                                                               args []))
                                                         (fun uu___1 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 match uu___1
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                 | FStar_Pervasives_Native.Some
                                                                    (applied_args,
                                                                    (last_arg,
                                                                    aqual))
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_STApp
                                                                    {
                                                                    Pulse_Syntax_Base.head
                                                                    =
                                                                    (Pulse_Syntax_Base.tm_fstar
                                                                    (FStar_Reflection_V2_Derived.mk_app
                                                                    head
                                                                    applied_args)
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    (FStar_Reflection_V2_Derived.mk_app
                                                                    head
                                                                    applied_args)));
                                                                    Pulse_Syntax_Base.arg_qual
                                                                    =
                                                                    ((match aqual
                                                                    with
                                                                    | FStar_Reflection_V2_Data.Q_Implicit
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Implicit
                                                                    | uu___3
                                                                    ->
                                                                    FStar_Pervasives_Native.None));
                                                                    Pulse_Syntax_Base.arg
                                                                    =
                                                                    (Pulse_Syntax_Base.tm_fstar
                                                                    last_arg
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    last_arg))
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (e.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    Pulse_Syntax_Base.default_effect_hint
                                                                    }))))
                                                   uu___1))))) uu___)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> FStar_Pervasives_Native.None)))) uu___1
        uu___

let (norm_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      FStar_TypeChecker_Core.tot_or_ghost ->
        Pulse_Syntax_Base.term ->
          unit ->
            FStar_Pervasives.norm_step Prims.list ->
              ((Pulse_Syntax_Base.term, unit) Prims.dtuple2, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun eff ->
        fun t0 ->
          fun d ->
            fun steps ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                         (Prims.of_int (804)) (Prims.of_int (12))
                         (Prims.of_int (804)) (Prims.of_int (24)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                         (Prims.of_int (804)) (Prims.of_int (27))
                         (Prims.of_int (815)) (Prims.of_int (18)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Pulse_Elaborate_Pure.elab_term t0))
                (fun uu___ ->
                   (fun t ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Base.fst"
                                    (Prims.of_int (806)) (Prims.of_int (6))
                                    (Prims.of_int (806)) (Prims.of_int (58)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Base.fst"
                                    (Prims.of_int (807)) (Prims.of_int (6))
                                    (Prims.of_int (815)) (Prims.of_int (18)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> ()))
                           (fun uu___ ->
                              (fun u_t_typing ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Base.fst"
                                               (Prims.of_int (809))
                                               (Prims.of_int (6))
                                               (Prims.of_int (809))
                                               (Prims.of_int (69)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Base.fst"
                                               (Prims.of_int (807))
                                               (Prims.of_int (6))
                                               (Prims.of_int (815))
                                               (Prims.of_int (18)))))
                                      (Obj.magic
                                         (Pulse_RuntimeUtils.norm_well_typed_term
                                            (Pulse_Typing.elab_env g)
                                            (Pulse_Elaborate_Pure.elab_term
                                               t0)
                                            FStar_TypeChecker_Core.E_Total ()
                                            () steps))
                                      (fun uu___ ->
                                         match uu___ with
                                         | FStar_Pervasives.Mkdtuple3
                                             (t', t'_typing, related_t_t') ->
                                             (match Pulse_Readback.readback_ty
                                                      t'
                                              with
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  FStar_Tactics_V2_Derived.fail
                                                    "Could not readback normalized type"
                                              | FStar_Pervasives_Native.Some
                                                  t'' ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       Prims.Mkdtuple2
                                                         (t'', ())))))) uu___)))
                     uu___)
let (norm_typing_inverse :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      FStar_TypeChecker_Core.tot_or_ghost ->
        Pulse_Syntax_Base.term ->
          unit ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.universe ->
                unit ->
                  FStar_Pervasives.norm_step Prims.list ->
                    (unit FStar_Pervasives_Native.option, unit)
                      FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun eff ->
        fun t0 ->
          fun d ->
            fun t1 ->
              fun u ->
                fun d1 ->
                  fun steps ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                               (Prims.of_int (826)) (Prims.of_int (47))
                               (Prims.of_int (828)) (Prims.of_int (54)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                               (Prims.of_int (826)) (Prims.of_int (3))
                               (Prims.of_int (838)) (Prims.of_int (15)))))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Base.fst"
                                     (Prims.of_int (827)) (Prims.of_int (15))
                                     (Prims.of_int (827)) (Prims.of_int (31)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Base.fst"
                                     (Prims.of_int (828)) (Prims.of_int (6))
                                     (Prims.of_int (828)) (Prims.of_int (54)))))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> ()))
                            (fun uu___ ->
                               (fun d11 ->
                                  Obj.magic
                                    (Pulse_RuntimeUtils.norm_well_typed_term
                                       (Pulse_Typing.elab_env g)
                                       (Pulse_Elaborate_Pure.elab_term t1)
                                       FStar_TypeChecker_Core.E_Total () ()
                                       steps)) uu___)))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              match uu___ with
                              | FStar_Pervasives.Mkdtuple3
                                  (t1', t1'_typing, related_t1_t1') ->
                                  (match Pulse_Readback.readback_ty t1' with
                                   | FStar_Pervasives_Native.Some t1_p ->
                                       if
                                         FStar_Reflection_V2_TermEq.term_eq
                                           (Pulse_Elaborate_Pure.elab_term t0)
                                           t1'
                                       then FStar_Pervasives_Native.Some ()
                                       else FStar_Pervasives_Native.None
                                   | uu___2 -> FStar_Pervasives_Native.None)))
let (norm_st_typing_inverse :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.universe ->
            Pulse_Syntax_Base.term ->
              unit ->
                FStar_Pervasives.norm_step Prims.list ->
                  ((unit, unit, unit) Pulse_Typing.st_typing
                     FStar_Pervasives_Native.option,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun t0 ->
        fun d ->
          fun u ->
            fun t1 ->
              fun d1 ->
                fun steps ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                             (Prims.of_int (851)) (Prims.of_int (8))
                             (Prims.of_int (851)) (Prims.of_int (24)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Base.fst"
                             (Prims.of_int (852)) (Prims.of_int (6))
                             (Prims.of_int (874)) (Prims.of_int (15)))))
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))
                    (fun uu___ ->
                       (fun d11 ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (854))
                                        (Prims.of_int (6))
                                        (Prims.of_int (854))
                                        (Prims.of_int (54)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Base.fst"
                                        (Prims.of_int (852))
                                        (Prims.of_int (6))
                                        (Prims.of_int (874))
                                        (Prims.of_int (15)))))
                               (Obj.magic
                                  (Pulse_RuntimeUtils.norm_well_typed_term
                                     (Pulse_Typing.elab_env g)
                                     (Pulse_Elaborate_Pure.elab_term t1)
                                     FStar_TypeChecker_Core.E_Total () ()
                                     steps))
                               (fun uu___ ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 ->
                                       match uu___ with
                                       | FStar_Pervasives.Mkdtuple3
                                           (t1', t1'_typing, related_t1_t1')
                                           ->
                                           (match Pulse_Readback.readback_ty
                                                    t1'
                                            with
                                            | FStar_Pervasives_Native.Some
                                                t1_p ->
                                                if
                                                  FStar_Reflection_V2_TermEq.term_eq
                                                    (Pulse_Elaborate_Pure.elab_term
                                                       t0) t1'
                                                then
                                                  FStar_Pervasives_Native.Some
                                                    (Pulse_Typing.T_Equiv
                                                       (g, e,
                                                         (Pulse_Syntax_Base.C_Tot
                                                            t0),
                                                         (Pulse_Syntax_Base.C_Tot
                                                            t1), d,
                                                         (Pulse_Typing.ST_TotEquiv
                                                            (g, t0, t1, u,
                                                              (), ()))))
                                                else
                                                  FStar_Pervasives_Native.None
                                            | uu___2 ->
                                                FStar_Pervasives_Native.None)))))
                         uu___)