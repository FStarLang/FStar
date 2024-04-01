open Prims
let (rt_recheck :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Tactics_NamedView.term ->
        FStar_Reflection_Types.typ ->
          unit ->
            ((unit, unit, unit) FStar_Reflection_Typing.tot_typing, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun gg ->
    fun g ->
      fun e ->
        fun ty ->
          fun uu___ ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (40)) (Prims.of_int (8))
                       (Prims.of_int (40)) (Prims.of_int (42)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (40)) (Prims.of_int (2))
                       (Prims.of_int (42)) (Prims.of_int (58)))))
              (Obj.magic
                 (FStar_Tactics_V2_Builtins.core_check_term g e ty
                    FStar_TypeChecker_Core.E_Total))
              (fun uu___1 ->
                 match uu___1 with
                 | (FStar_Pervasives_Native.Some tok, uu___2) ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___3 ->
                          FStar_Reflection_Typing.T_Token
                            (g, e, (FStar_TypeChecker_Core.E_Total, ty), ()))
                 | (FStar_Pervasives_Native.None, uu___2) ->
                     FStar_Tactics_V2_Derived.fail
                       "Checker.WithInv: rt_recheck failed")
let (recheck :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.typ ->
        unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun ty -> fun uu___ -> Pulse_Checker_Pure.core_check_tot_term g e ty
let (remove_iname :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun inames ->
    fun i ->
      Pulse_Syntax_Pure.wr
        (Pulse_Reflection_Util.remove_inv_tm
           (Pulse_Elaborate_Pure.elab_term inames)
           (Pulse_Elaborate_Pure.elab_term i))
        (Pulse_RuntimeUtils.range_of_term inames)
let (add_iname :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun inames ->
    fun i ->
      Pulse_Syntax_Pure.wr
        (Pulse_Reflection_Util.add_inv_tm
           (Pulse_Elaborate_Pure.elab_term inames)
           (Pulse_Elaborate_Pure.elab_term i))
        (Pulse_RuntimeUtils.range_of_term inames)
let (all_inames : Pulse_Syntax_Base.term) =
  Pulse_Syntax_Pure.wr Pulse_Syntax_Pure.tm_all_inames FStar_Range.range_0




let (disjointness_remove_i_i :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun inames ->
             fun i ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ())))
          uu___2 uu___1 uu___
let (add_remove_inverse :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        unit -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun inames ->
      fun i ->
        fun inames_typing ->
          fun i_typing ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (142)) (Prims.of_int (3))
                       (Prims.of_int (146)) (Prims.of_int (19)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (148)) (Prims.of_int (2))
                       (Prims.of_int (160)) (Prims.of_int (19)))))
              (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))
              (fun uu___ ->
                 (fun typing ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.WithInv.fst"
                                  (Prims.of_int (148)) (Prims.of_int (8))
                                  (Prims.of_int (148)) (Prims.of_int (61)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.WithInv.fst"
                                  (Prims.of_int (148)) (Prims.of_int (2))
                                  (Prims.of_int (160)) (Prims.of_int (19)))))
                         (Obj.magic
                            (Pulse_Checker_Pure.try_check_prop_validity g
                               (Pulse_Typing.tm_inames_subset
                                  (add_iname (remove_iname inames i) i)
                                  inames) ()))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | FStar_Pervasives_Native.None ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.WithInv.fst"
                                                    (Prims.of_int (151))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (158))
                                                    (Prims.of_int (5)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.WithInv.fst"
                                                    (Prims.of_int (151))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (158))
                                                    (Prims.of_int (5)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (151))
                                                          (Prims.of_int (20))
                                                          (Prims.of_int (158))
                                                          (Prims.of_int (5)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (151))
                                                          (Prims.of_int (20))
                                                          (Prims.of_int (158))
                                                          (Prims.of_int (5)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.WithInv.fst"
                                                                (Prims.of_int (153))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (157))
                                                                (Prims.of_int (65)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.WithInv.fst"
                                                                (Prims.of_int (151))
                                                                (Prims.of_int (20))
                                                                (Prims.of_int (158))
                                                                (Prims.of_int (5)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (15)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (65)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (15)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (15)))))
                                                                   (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    (add_iname
                                                                    (remove_iname
                                                                    inames i)
                                                                    i)))
                                                                   (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Inferred the following invariants were opened: ")
                                                                    uu___1))))
                                                             (fun uu___1 ->
                                                                (fun uu___1
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    inames))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "But expected to only open: ")
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___1
                                                                    uu___2))))
                                                                  uu___1)))
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               [uu___1]))))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         (Pulse_PP.text
                                                            "Failed to prove that only the following invariants are opened")
                                                         :: uu___1))))
                                           (fun uu___1 ->
                                              (fun uu___1 ->
                                                 Obj.magic
                                                   (Pulse_Typing_Env.fail_doc
                                                      g
                                                      FStar_Pervasives_Native.None
                                                      uu___1)) uu___1)))
                               | FStar_Pervasives_Native.Some tok ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 -> ())))) uu___)))
                   uu___)
let rec (find_inv :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.term ->
          (Pulse_Syntax_Base.term, Pulse_Syntax_Base.term, unit, unit, 
            unit) FStar_Pervasives.dtuple5 FStar_Pervasives_Native.option)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun i ->
          match Pulse_Syntax_Pure.inspect_term pre with
          | Pulse_Syntax_Pure.Tm_Inv (i', p) ->
              if Pulse_Syntax_Base.eq_tm i i'
              then
                let frame = Pulse_Syntax_Pure.tm_emp in
                FStar_Pervasives_Native.Some
                  (FStar_Pervasives.Mkdtuple5 (p, frame, (), (), ()))
              else FStar_Pervasives_Native.None
          | Pulse_Syntax_Pure.Tm_Star (l, r) ->
              (match find_inv g l () i with
               | FStar_Pervasives_Native.Some res ->
                   let uu___ = res in
                   (match uu___ with
                    | FStar_Pervasives.Mkdtuple5
                        (p, frame, uu___1, uu___2, uu___3) ->
                        FStar_Pervasives_Native.Some
                          (FStar_Pervasives.Mkdtuple5
                             (p, (Pulse_Syntax_Pure.tm_star frame r), (), (),
                               ())))
               | FStar_Pervasives_Native.None ->
                   (match find_inv g r () i with
                    | FStar_Pervasives_Native.Some res ->
                        let uu___ = res in
                        (match uu___ with
                         | FStar_Pervasives.Mkdtuple5
                             (p, frame, uu___1, uu___2, uu___3) ->
                             FStar_Pervasives_Native.Some
                               (FStar_Pervasives.Mkdtuple5
                                  (p, (Pulse_Syntax_Pure.tm_star l frame),
                                    (), (), ())))
                    | uu___ -> FStar_Pervasives_Native.None))
          | uu___ -> FStar_Pervasives_Native.None
let (find_inv_post :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.universe ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            unit ->
              unit ->
                Pulse_Syntax_Base.term ->
                  ((Pulse_Syntax_Base.term, Pulse_Syntax_Base.term, unit,
                     unit, unit) FStar_Pervasives.dtuple5
                     FStar_Pervasives_Native.option,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun x ->
      fun u ->
        fun ret_ty ->
          fun post ->
            fun ret_ty_typing ->
              fun post_typing ->
                fun i ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                             (Prims.of_int (225)) (Prims.of_int (20))
                             (Prims.of_int (225)) (Prims.of_int (57)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                             (Prims.of_int (225)) (Prims.of_int (60))
                             (Prims.of_int (233)) (Prims.of_int (71)))))
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          Pulse_Syntax_Naming.open_term_nv post
                            (Pulse_Syntax_Base.ppname_default, x)))
                    (fun uu___ ->
                       (fun post_opened ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.WithInv.fst"
                                        (Prims.of_int (226))
                                        (Prims.of_int (12))
                                        (Prims.of_int (226))
                                        (Prims.of_int (50)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.WithInv.fst"
                                        (Prims.of_int (227))
                                        (Prims.of_int (2))
                                        (Prims.of_int (233))
                                        (Prims.of_int (71)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___ ->
                                     find_inv
                                       (Pulse_Typing_Env.push_binding g x
                                          Pulse_Syntax_Base.ppname_default
                                          ret_ty) post_opened () i))
                               (fun uu___ ->
                                  (fun res ->
                                     match res with
                                     | FStar_Pervasives_Native.None ->
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___ ->
                                                    FStar_Pervasives_Native.None)))
                                     | FStar_Pervasives_Native.Some
                                         (FStar_Pervasives.Mkdtuple5
                                         (p, frame, inv_typing, frame_typing,
                                          d_eq))
                                         ->
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (230))
                                                          (Prims.of_int (53))
                                                          (Prims.of_int (230))
                                                          (Prims.of_int (65)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (231))
                                                          (Prims.of_int (55))
                                                          (Prims.of_int (233))
                                                          (Prims.of_int (71)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___ -> ()))
                                                 (fun uu___ ->
                                                    (fun frame_typing1 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (71)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (71)))))
                                                            (Obj.magic
                                                               (recheck g
                                                                  (Pulse_Syntax_Pure.tm_inv
                                                                    i p)
                                                                  Pulse_Syntax_Pure.tm_vprop
                                                                  ()))
                                                            (fun
                                                               tm_inv_typing
                                                               ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p,
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    frame x),
                                                                    (), (),
                                                                    ()))))))
                                                      uu___)))) uu___)))
                         uu___)
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Checker_Base.check_t ->
                ((unit, unit, unit) Pulse_Checker_Base.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              fun check1 ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (278)) (Prims.of_int (47))
                           (Prims.of_int (278)) (Prims.of_int (53)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (278)) Prims.int_one
                           (Prims.of_int (437)) (Prims.of_int (59)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> t.Pulse_Syntax_Base.term1))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | Pulse_Syntax_Base.Tm_WithInv
                            { Pulse_Syntax_Base.name1 = i;
                              Pulse_Syntax_Base.body6 = body;
                              Pulse_Syntax_Base.returns_inv = returns_inv;_}
                            ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (280))
                                          (Prims.of_int (4))
                                          (Prims.of_int (291))
                                          (Prims.of_int (67)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (293))
                                          (Prims.of_int (2))
                                          (Prims.of_int (437))
                                          (Prims.of_int (59)))))
                                 (match (returns_inv, post_hint) with
                                  | (FStar_Pervasives_Native.None,
                                     FStar_Pervasives_Native.Some p) ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 -> p)))
                                  | (FStar_Pervasives_Native.Some (b, p),
                                     FStar_Pervasives_Native.None) ->
                                      Obj.magic
                                        (Obj.repr
                                           (Pulse_Checker_Base.intro_post_hint
                                              g
                                              Pulse_Syntax_Base.EffectAnnotSTT
                                              (FStar_Pervasives_Native.Some
                                                 (b.Pulse_Syntax_Base.binder_ty))
                                              p))
                                  | (FStar_Pervasives_Native.Some
                                     (uu___1, p),
                                     FStar_Pervasives_Native.Some q) ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.WithInv.fst"
                                                       (Prims.of_int (287))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (289))
                                                       (Prims.of_int (60)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.WithInv.fst"
                                                       (Prims.of_int (286))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (289))
                                                       (Prims.of_int (60)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.WithInv.fst"
                                                             (Prims.of_int (287))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (289))
                                                             (Prims.of_int (60)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.WithInv.fst"
                                                             (Prims.of_int (287))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (289))
                                                             (Prims.of_int (60)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.WithInv.fst"
                                                                   (Prims.of_int (288))
                                                                   (Prims.of_int (10))
                                                                   (Prims.of_int (288))
                                                                   (Prims.of_int (57)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.WithInv.fst"
                                                                   (Prims.of_int (287))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (289))
                                                                   (Prims.of_int (60)))))
                                                          (Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (57)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (57)))))
                                                                (Obj.magic
                                                                   (Pulse_PP.pp
                                                                    Pulse_PP.printable_fstar_term
                                                                    p))
                                                                (fun uu___2
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "First postcondition:")
                                                                    uu___2))))
                                                          (fun uu___2 ->
                                                             (fun uu___2 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_post_hint_t
                                                                    q))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Second postcondition:")
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    [uu___3]))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___2 ::
                                                                    uu___3))))
                                                               uu___2)))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            (FStar_Pprint.doc_of_string
                                                               "Fatal: multiple annotated postconditions on with_invariant")
                                                            :: uu___2))))
                                              (fun uu___2 ->
                                                 (fun uu___2 ->
                                                    Obj.magic
                                                      (Pulse_Typing_Env.fail_doc
                                                         g
                                                         (FStar_Pervasives_Native.Some
                                                            (t.Pulse_Syntax_Base.range1))
                                                         uu___2)) uu___2)))
                                  | (uu___1, uu___2) ->
                                      Obj.magic
                                        (Obj.repr
                                           (Pulse_Typing_Env.fail g
                                              (FStar_Pervasives_Native.Some
                                                 (t.Pulse_Syntax_Base.range1))
                                              "Fatal: no post hint on with_invariant")))
                                 (fun uu___1 ->
                                    (fun post_hint1 ->
                                       match post_hint1.Pulse_Typing.effect_annot
                                       with
                                       | Pulse_Syntax_Base.EffectAnnotGhost
                                           uu___1 ->
                                           Obj.magic
                                             (Pulse_Typing_Env.fail_doc g
                                                (FStar_Pervasives_Native.Some
                                                   (t.Pulse_Syntax_Base.range1))
                                                [FStar_Pprint.doc_of_string
                                                   "Cannot open invariants in a 'ghost' context"])
                                       | uu___1 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.WithInv.fst"
                                                         (Prims.of_int (302))
                                                         (Prims.of_int (21))
                                                         (Prims.of_int (302))
                                                         (Prims.of_int (31)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.WithInv.fst"
                                                         (Prims.of_int (302))
                                                         (Prims.of_int (34))
                                                         (Prims.of_int (437))
                                                         (Prims.of_int (59)))))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      body.Pulse_Syntax_Base.range1))
                                                (fun uu___2 ->
                                                   (fun body_range ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (52)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 Pulse_RuntimeUtils.range_of_term
                                                                   i))
                                                           (fun uu___2 ->
                                                              (fun i_range ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    find_inv
                                                                    g pre ()
                                                                    i))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun res
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    res
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    i_range)
                                                                    "Cannot find inv in the context"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    res))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p,
                                                                    pre_frame,
                                                                    inv_typing,
                                                                    pre_frame_typing,
                                                                    d_pre_frame_eq))
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Pure.tm_star
                                                                    p
                                                                    pre_frame))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    pre_body
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    pre_body_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    post_hint1.Pulse_Typing.ret_ty))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (recheck
                                                                    g
                                                                    post_hint1.Pulse_Typing.ret_ty
                                                                    (Pulse_Syntax_Pure.tm_type
                                                                    post_hint1.Pulse_Typing.u)
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    post_hint_ret_ty_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (recheck
                                                                    g'
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    post_hint1.Pulse_Typing.post
                                                                    (Pulse_Syntax_Base.ppname_default,
                                                                    x))
                                                                    Pulse_Syntax_Pure.tm_vprop
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    post_hint_post_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (find_inv_post
                                                                    g x
                                                                    post_hint1.Pulse_Typing.u
                                                                    post_hint1.Pulse_Typing.ret_ty
                                                                    post_hint1.Pulse_Typing.post
                                                                    () () i))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun res1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    res1
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    i_range)
                                                                    "Cannot find inv in the postcondition"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    res1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p',
                                                                    post_frame,
                                                                    uu___6,
                                                                    post_frame_typing,
                                                                    d_post_frame_equiv))
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Pure.tm_star
                                                                    p
                                                                    post_frame))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    post_body
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match 
                                                                    post_hint1.Pulse_Typing.effect_annot
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotSTT
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (all_inames,
                                                                    ())
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    {
                                                                    Pulse_Syntax_Base.opens1
                                                                    = opens;_}
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (opens,
                                                                    ())))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (opens,
                                                                    opens_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    remove_iname
                                                                    opens i))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    opens_remove_i
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    {
                                                                    Pulse_Syntax_Base.opens1
                                                                    =
                                                                    opens_remove_i
                                                                    }))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    effect_annot
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    ())
                                                                    uu___9))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    effect_annot_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    {
                                                                    Pulse_Typing.g
                                                                    = g;
                                                                    Pulse_Typing.effect_annot
                                                                    =
                                                                    effect_annot;
                                                                    Pulse_Typing.effect_annot_typing
                                                                    =
                                                                    effect_annot_typing;
                                                                    Pulse_Typing.ret_ty
                                                                    =
                                                                    (post_hint1.Pulse_Typing.ret_ty);
                                                                    Pulse_Typing.u
                                                                    =
                                                                    (post_hint1.Pulse_Typing.u);
                                                                    Pulse_Typing.ty_typing
                                                                    = ();
                                                                    Pulse_Typing.post
                                                                    =
                                                                    post_body;
                                                                    Pulse_Typing.x
                                                                    = x;
                                                                    Pulse_Typing.post_typing_src
                                                                    = ();
                                                                    Pulse_Typing.post_typing
                                                                    = ()
                                                                    }))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    post_hint_body
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "with_inv_body"))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    ppname ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (check1 g
                                                                    pre_body
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint_body)
                                                                    ppname
                                                                    body))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g
                                                                    pre_body
                                                                    post_hint_body
                                                                    r ppname))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> c_body))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (inames,
                                                                    obs, st)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    ((Pulse_Reflection_Util.add_inv_tm
                                                                    inames i),
                                                                    obs,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    =
                                                                    (st.Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.res
                                                                    =
                                                                    (st.Pulse_Syntax_Base.res);
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (post_hint1.Pulse_Typing.post)
                                                                    })))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    c_out ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (disjointness_remove_i_i
                                                                    g opens i))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun tok
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Typing.T_Equiv
                                                                    (g,
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT_Atomic)
                                                                    (Pulse_Syntax_Base.Tm_WithInv
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = i;
                                                                    Pulse_Syntax_Base.body6
                                                                    = body1;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })),
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    ((Pulse_Reflection_Util.add_inv_tm
                                                                    inames i),
                                                                    obs,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    =
                                                                    (st.Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.res
                                                                    =
                                                                    (st.Pulse_Syntax_Base.res);
                                                                    Pulse_Syntax_Base.pre
                                                                    =
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i p)
                                                                    pre_frame);
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i p)
                                                                    post_frame)
                                                                    })),
                                                                    c_out,
                                                                    (Pulse_Typing.T_WithInv
                                                                    (g, i, p,
                                                                    body1,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (inames,
                                                                    obs,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    =
                                                                    (st.Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.res
                                                                    =
                                                                    (st.Pulse_Syntax_Base.res);
                                                                    Pulse_Syntax_Base.pre
                                                                    =
                                                                    pre_frame;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    post_frame
                                                                    })), (),
                                                                    (),
                                                                    body_typing,
                                                                    ())),
                                                                    (Pulse_Typing.ST_VPropEquiv
                                                                    (g,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    ((Pulse_Reflection_Util.add_inv_tm
                                                                    inames i),
                                                                    obs,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    =
                                                                    (st.Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.res
                                                                    =
                                                                    (st.Pulse_Syntax_Base.res);
                                                                    Pulse_Syntax_Base.pre
                                                                    =
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i p)
                                                                    pre_frame);
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i p)
                                                                    post_frame)
                                                                    })),
                                                                    c_out, x,
                                                                    (), (),
                                                                    (),
                                                                    (FStar_Reflection_Typing.Rel_refl
                                                                    ((Pulse_Typing.elab_env
                                                                    g),
                                                                    (Pulse_Elaborate_Pure.elab_term
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    ((Pulse_Reflection_Util.add_inv_tm
                                                                    inames i),
                                                                    obs,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    =
                                                                    (st.Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.res
                                                                    =
                                                                    (st.Pulse_Syntax_Base.res);
                                                                    Pulse_Syntax_Base.pre
                                                                    =
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i p)
                                                                    pre_frame);
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i p)
                                                                    post_frame)
                                                                    })))),
                                                                    FStar_Reflection_Typing.R_Eq)),
                                                                    (), ())))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun d ->
                                                                    match 
                                                                    post_hint1.Pulse_Typing.effect_annot
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> c_out))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (add_inv,
                                                                    obs1,
                                                                    st1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (add_remove_inverse
                                                                    g opens i
                                                                    () ()))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun tok1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (opens,
                                                                    obs1,
                                                                    st1)))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    c_out1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g,
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT_Atomic)
                                                                    (Pulse_Syntax_Base.Tm_WithInv
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = i;
                                                                    Pulse_Syntax_Base.body6
                                                                    = body1;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })),
                                                                    c_out,
                                                                    (Pulse_Syntax_Base.C_STAtomic
                                                                    (opens,
                                                                    obs1,
                                                                    st1)), d,
                                                                    (Pulse_Typing.STS_AtomicInvs
                                                                    (g, st1,
                                                                    add_inv,
                                                                    opens,
                                                                    obs1,
                                                                    obs1, ())))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT_Atomic)
                                                                    (Pulse_Syntax_Base.Tm_WithInv
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = i;
                                                                    Pulse_Syntax_Base.body6
                                                                    = body1;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })),
                                                                    c_out1,
                                                                    d1))
                                                                    res_ppname))
                                                                    uu___13)))
                                                                    uu___13)))
                                                                    uu___13)))
                                                                    uu___12))
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotSTT
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g,
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT_Atomic)
                                                                    (Pulse_Syntax_Base.Tm_WithInv
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = i;
                                                                    Pulse_Syntax_Base.body6
                                                                    = body1;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })),
                                                                    c_out,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_out)),
                                                                    d,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g,
                                                                    c_out)))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT_Atomic)
                                                                    (Pulse_Syntax_Base.Tm_WithInv
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = i;
                                                                    Pulse_Syntax_Base.body6
                                                                    = body1;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })),
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_out)),
                                                                    d1))
                                                                    res_ppname))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                uu___2)))
                                                     uu___2))) uu___1)))
                       uu___)