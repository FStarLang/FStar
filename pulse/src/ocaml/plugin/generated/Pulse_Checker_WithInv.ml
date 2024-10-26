open Prims
let (rt_recheck :
  Pulse_Typing_Env.env ->
    FStarC_Reflection_Types.env ->
      FStar_Tactics_NamedView.term ->
        FStarC_Reflection_Types.typ ->
          unit ->
            ((unit, unit, unit) FStar_Reflection_Typing.tot_typing, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun gg ->
    fun g ->
      fun e ->
        fun ty ->
          fun uu___ ->
            let uu___1 =
              FStarC_Tactics_V2_Builtins.core_check_term g e ty
                FStarC_TypeChecker_Core.E_Total in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (35)) (Prims.of_int (8))
                       (Prims.of_int (35)) (Prims.of_int (42)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (35)) (Prims.of_int (2))
                       (Prims.of_int (37)) (Prims.of_int (58)))))
              (Obj.magic uu___1)
              (fun uu___2 ->
                 match uu___2 with
                 | (FStar_Pervasives_Native.Some tok, uu___3) ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___4 ->
                          FStar_Reflection_Typing.T_Token
                            (g, e, (FStarC_TypeChecker_Core.E_Total, ty), ()))
                 | (FStar_Pervasives_Native.None, uu___3) ->
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
      Pulse_Syntax_Pure.wr (Pulse_Reflection_Util.remove_inv_tm inames i)
        (Pulse_RuntimeUtils.range_of_term inames)
let (add_iname :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun inames ->
    fun i ->
      Pulse_Syntax_Pure.wr (Pulse_Syntax_Pure.tm_add_inv inames i)
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
            let uu___ =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ())) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (102)) (Prims.of_int (3))
                       (Prims.of_int (106)) (Prims.of_int (19)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (108)) (Prims.of_int (2))
                       (Prims.of_int (119)) (Prims.of_int (19)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun typing ->
                    let uu___1 =
                      Pulse_Checker_Pure.try_check_prop_validity g
                        (Pulse_Typing.tm_inames_subset
                           (add_iname (remove_iname inames i) i) inames) () in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.WithInv.fst"
                                  (Prims.of_int (108)) (Prims.of_int (8))
                                  (Prims.of_int (108)) (Prims.of_int (61)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.WithInv.fst"
                                  (Prims.of_int (108)) (Prims.of_int (2))
                                  (Prims.of_int (119)) (Prims.of_int (19)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun uu___2 ->
                               match uu___2 with
                               | FStar_Pervasives_Native.None ->
                                   Obj.magic
                                     (Obj.repr
                                        (let uu___3 =
                                           let uu___4 =
                                             let uu___5 =
                                               let uu___6 =
                                                 let uu___7 =
                                                   Pulse_PP.pp
                                                     Pulse_PP.printable_term
                                                     (add_iname
                                                        (remove_iname inames
                                                           i) i) in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.WithInv.fst"
                                                            (Prims.of_int (113))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (115))
                                                            (Prims.of_int (15)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.WithInv.fst"
                                                            (Prims.of_int (112))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (115))
                                                            (Prims.of_int (15)))))
                                                   (Obj.magic uu___7)
                                                   (fun uu___8 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___9 ->
                                                           FStar_Pprint.prefix
                                                             (Prims.of_int (4))
                                                             Prims.int_one
                                                             (Pulse_PP.text
                                                                "Inferred the following invariants were opened: ")
                                                             uu___8)) in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (112))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (115))
                                                          (Prims.of_int (15)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (112))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (116))
                                                          (Prims.of_int (65)))))
                                                 (Obj.magic uu___6)
                                                 (fun uu___7 ->
                                                    (fun uu___7 ->
                                                       let uu___8 =
                                                         let uu___9 =
                                                           Pulse_PP.pp
                                                             Pulse_PP.printable_term
                                                             inames in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (65)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (65)))))
                                                           (Obj.magic uu___9)
                                                           (fun uu___10 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___11
                                                                   ->
                                                                   FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "But expected to only open: ")
                                                                    uu___10)) in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (65)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (65)))))
                                                            (Obj.magic uu___8)
                                                            (fun uu___9 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___10
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___7
                                                                    uu___9))))
                                                      uu___7) in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.WithInv.fst"
                                                        (Prims.of_int (112))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (116))
                                                        (Prims.of_int (65)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.WithInv.fst"
                                                        (Prims.of_int (110))
                                                        (Prims.of_int (20))
                                                        (Prims.of_int (117))
                                                        (Prims.of_int (5)))))
                                               (Obj.magic uu___5)
                                               (fun uu___6 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___7 -> [uu___6])) in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.WithInv.fst"
                                                      (Prims.of_int (110))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (117))
                                                      (Prims.of_int (5)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.WithInv.fst"
                                                      (Prims.of_int (110))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (117))
                                                      (Prims.of_int (5)))))
                                             (Obj.magic uu___4)
                                             (fun uu___5 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___6 ->
                                                     (Pulse_PP.text
                                                        "Failed to prove that only the following invariants are opened")
                                                     :: uu___5)) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.WithInv.fst"
                                                    (Prims.of_int (110))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (117))
                                                    (Prims.of_int (5)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.WithInv.fst"
                                                    (Prims.of_int (110))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (117))
                                                    (Prims.of_int (5)))))
                                           (Obj.magic uu___3)
                                           (fun uu___4 ->
                                              (fun uu___4 ->
                                                 Obj.magic
                                                   (Pulse_Typing_Env.fail_doc
                                                      g
                                                      FStar_Pervasives_Native.None
                                                      uu___4)) uu___4)))
                               | FStar_Pervasives_Native.Some tok ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> ())))) uu___2)))
                   uu___1)
let rec (find_inv :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.term ->
          ((Pulse_Syntax_Base.term, Pulse_Syntax_Base.term, unit, unit, 
             unit) FStar_Pervasives.dtuple5 FStar_Pervasives_Native.option,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun pre ->
               fun pre_typing ->
                 fun i ->
                   match Pulse_Syntax_Pure.inspect_term pre with
                   | Pulse_Syntax_Pure.Tm_Inv (i', p) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ ->
                                  if Pulse_Syntax_Base.eq_tm i i'
                                  then
                                    FStar_Pervasives_Native.Some
                                      (FStar_Pervasives.Mkdtuple5
                                         (p, Pulse_Syntax_Pure.tm_emp, (),
                                           (), ()))
                                  else FStar_Pervasives_Native.None)))
                   | Pulse_Syntax_Pure.Tm_Star (l, r) ->
                       Obj.magic
                         (Obj.repr
                            (let uu___ = find_inv g l () i in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.WithInv.fst"
                                        (Prims.of_int (142))
                                        (Prims.of_int (10))
                                        (Prims.of_int (142))
                                        (Prims.of_int (37)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.WithInv.fst"
                                        (Prims.of_int (142))
                                        (Prims.of_int (4))
                                        (Prims.of_int (151))
                                        (Prims.of_int (17)))))
                               (Obj.magic uu___)
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | FStar_Pervasives_Native.Some res ->
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    match res with
                                                    | FStar_Pervasives.Mkdtuple5
                                                        (p, frame, uu___3,
                                                         uu___4, uu___5)
                                                        ->
                                                        FStar_Pervasives_Native.Some
                                                          (FStar_Pervasives.Mkdtuple5
                                                             (p,
                                                               (Pulse_Syntax_Pure.tm_star
                                                                  frame r),
                                                               (), (), ())))))
                                     | FStar_Pervasives_Native.None ->
                                         Obj.magic
                                           (Obj.repr
                                              (let uu___2 = find_inv g r () i in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (147))
                                                          (Prims.of_int (12))
                                                          (Prims.of_int (147))
                                                          (Prims.of_int (39)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (147))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (151))
                                                          (Prims.of_int (17)))))
                                                 (Obj.magic uu___2)
                                                 (fun uu___3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 ->
                                                         match uu___3 with
                                                         | FStar_Pervasives_Native.Some
                                                             res ->
                                                             (match res with
                                                              | FStar_Pervasives.Mkdtuple5
                                                                  (p, frame,
                                                                   uu___5,
                                                                   uu___6,
                                                                   uu___7)
                                                                  ->
                                                                  FStar_Pervasives_Native.Some
                                                                    (
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (p,
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    l frame),
                                                                    (), (),
                                                                    ())))
                                                         | uu___5 ->
                                                             FStar_Pervasives_Native.None)))))
                                    uu___1)))
                   | uu___ ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> FStar_Pervasives_Native.None))))
            uu___3 uu___2 uu___1 uu___
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
                  let uu___ =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 ->
                            Pulse_Syntax_Naming.open_term_nv post
                              (Pulse_Syntax_Base.ppname_default, x))) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                             (Prims.of_int (172)) (Prims.of_int (20))
                             (Prims.of_int (172)) (Prims.of_int (57)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                             (Prims.of_int (172)) (Prims.of_int (60))
                             (Prims.of_int (183)) (Prims.of_int (114)))))
                    (Obj.magic uu___)
                    (fun uu___1 ->
                       (fun post_opened ->
                          let uu___1 =
                            Pulse_Checker_Prover.normalize_slprop_welltyped
                              (Pulse_Typing_Env.push_binding g x
                                 Pulse_Syntax_Base.ppname_default ret_ty)
                              post_opened () in
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.WithInv.fst"
                                        (Prims.of_int (174))
                                        (Prims.of_int (4))
                                        (Prims.of_int (174))
                                        (Prims.of_int (95)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.WithInv.fst"
                                        (Prims.of_int (172))
                                        (Prims.of_int (60))
                                        (Prims.of_int (183))
                                        (Prims.of_int (114)))))
                               (Obj.magic uu___1)
                               (fun uu___2 ->
                                  (fun uu___2 ->
                                     match uu___2 with
                                     | FStar_Pervasives.Mkdtuple3
                                         (post_opened1, post_equiv,
                                          post_typing1)
                                         ->
                                         let uu___3 =
                                           find_inv
                                             (Pulse_Typing_Env.push_binding g
                                                x
                                                Pulse_Syntax_Base.ppname_default
                                                ret_ty) post_opened1 () i in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.WithInv.fst"
                                                       (Prims.of_int (176))
                                                       (Prims.of_int (12))
                                                       (Prims.of_int (176))
                                                       (Prims.of_int (34)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.WithInv.fst"
                                                       (Prims.of_int (177))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (183))
                                                       (Prims.of_int (114)))))
                                              (Obj.magic uu___3)
                                              (fun uu___4 ->
                                                 (fun res ->
                                                    match res with
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   FStar_Pervasives_Native.None)))
                                                    | FStar_Pervasives_Native.Some
                                                        (FStar_Pervasives.Mkdtuple5
                                                        (p, frame,
                                                         inv_typing,
                                                         frame_typing, d_eq))
                                                        ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (let uu___4 =
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ())) in
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (66)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (114)))))
                                                                (Obj.magic
                                                                   uu___4)
                                                                (fun uu___5
                                                                   ->
                                                                   (fun
                                                                    frame_typing1
                                                                    ->
                                                                    let uu___5
                                                                    =
                                                                    recheck g
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i p)
                                                                    Pulse_Syntax_Pure.tm_slprop
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (114)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    tm_inv_typing
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p,
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    frame x),
                                                                    (), (),
                                                                    ()))))))
                                                                    uu___5))))
                                                   uu___4))) uu___2))) uu___1)
let (atomic_or_ghost_with_inames_and_pre_post :
  Pulse_Syntax_Base.comp ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp)
  =
  fun c ->
    fun inames ->
      fun pre ->
        fun post ->
          match c with
          | Pulse_Syntax_Base.C_STAtomic (uu___, obs, s) ->
              Pulse_Syntax_Base.C_STAtomic
                (inames, obs,
                  {
                    Pulse_Syntax_Base.u = (s.Pulse_Syntax_Base.u);
                    Pulse_Syntax_Base.res = (s.Pulse_Syntax_Base.res);
                    Pulse_Syntax_Base.pre = pre;
                    Pulse_Syntax_Base.post = post
                  })
          | Pulse_Syntax_Base.C_STGhost (uu___, s) ->
              Pulse_Syntax_Base.C_STGhost
                (inames,
                  {
                    Pulse_Syntax_Base.u = (s.Pulse_Syntax_Base.u);
                    Pulse_Syntax_Base.res = (s.Pulse_Syntax_Base.res);
                    Pulse_Syntax_Base.pre = pre;
                    Pulse_Syntax_Base.post = post
                  })
let rec (__withinv_post :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit ->
              unit ->
                ((Pulse_Syntax_Base.term, unit) Prims.dtuple2
                   FStar_Pervasives_Native.option,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun g ->
                   fun p ->
                     fun i ->
                       fun post ->
                         fun p_typing ->
                           fun i_typing ->
                             fun post_typing ->
                               if
                                 Pulse_Syntax_Base.eq_tm post
                                   (Pulse_Syntax_Pure.tm_later p)
                               then
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___ ->
                                            FStar_Pervasives_Native.Some
                                              (Prims.Mkdtuple2
                                                 ((Pulse_Syntax_Pure.tm_inv i
                                                     p), ())))))
                               else
                                 Obj.magic
                                   (Obj.repr
                                      (match Pulse_Syntax_Pure.inspect_term
                                               post
                                       with
                                       | Pulse_Syntax_Pure.Tm_Star (l, r) ->
                                           Obj.repr
                                             (let uu___1 =
                                                __withinv_post g p i l () ()
                                                  () in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.WithInv.fst"
                                                         (Prims.of_int (216))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (216))
                                                         (Prims.of_int (74)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.WithInv.fst"
                                                         (Prims.of_int (218))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (226))
                                                         (Prims.of_int (16)))))
                                                (Obj.magic uu___1)
                                                (fun uu___2 ->
                                                   (fun res ->
                                                      match res with
                                                      | FStar_Pervasives_Native.Some
                                                          (Prims.Mkdtuple2
                                                          (l', uu___2)) ->
                                                          Obj.magic
                                                            (Obj.repr
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___3
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Pure.tm_star
                                                                    l' r),
                                                                    ())))))
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          Obj.magic
                                                            (Obj.repr
                                                               (let uu___2 =
                                                                  __withinv_post
                                                                    g p i r
                                                                    () () () in
                                                                FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (80)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (29)))))
                                                                  (Obj.magic
                                                                    uu___2)
                                                                  (fun res1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match res1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (r',
                                                                    uu___4))
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Pure.tm_star
                                                                    l r'),
                                                                    ()))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None)))))
                                                     uu___2))
                                       | uu___1 ->
                                           Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   FStar_Pervasives_Native.None)))))
                  uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (withinv_post :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          unit ->
            unit ->
              unit ->
                ((Pulse_Syntax_Base.term, unit) Prims.dtuple2
                   FStar_Pervasives_Native.option,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun p ->
      fun i ->
        fun post ->
          fun p_typing ->
            fun i_typing ->
              fun post_typing ->
                let uu___ =
                  Pulse_Checker_Prover.normalize_slprop_welltyped g p () in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (237)) (Prims.of_int (29))
                           (Prims.of_int (237)) (Prims.of_int (75)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (236)) (Prims.of_int (51))
                           (Prims.of_int (239)) (Prims.of_int (61)))))
                  (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun uu___1 ->
                        match uu___1 with
                        | FStar_Pervasives.Mkdtuple3 (p1, uu___2, p_typing1)
                            ->
                            let uu___3 =
                              Pulse_Checker_Prover.normalize_slprop_welltyped
                                g post () in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (238))
                                          (Prims.of_int (35))
                                          (Prims.of_int (238))
                                          (Prims.of_int (87)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (237))
                                          (Prims.of_int (78))
                                          (Prims.of_int (239))
                                          (Prims.of_int (61)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    (fun uu___4 ->
                                       match uu___4 with
                                       | FStar_Pervasives.Mkdtuple3
                                           (post1, uu___5, post_typing1) ->
                                           Obj.magic
                                             (__withinv_post g p1 i post1 ()
                                                () ())) uu___4))) uu___1)
let (check0 :
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
              fun check ->
                let uu___ =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> t.Pulse_Syntax_Base.term1)) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (252)) (Prims.of_int (47))
                           (Prims.of_int (252)) (Prims.of_int (53)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (252)) Prims.int_one
                           (Prims.of_int (481)) (Prims.of_int (57)))))
                  (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun uu___1 ->
                        match uu___1 with
                        | Pulse_Syntax_Base.Tm_WithInv
                            { Pulse_Syntax_Base.name1 = i;
                              Pulse_Syntax_Base.body6 = body;
                              Pulse_Syntax_Base.returns_inv = returns_inv;_}
                            ->
                            let uu___2 =
                              Pulse_Checker_Pure.check_tot_term g i
                                Pulse_Syntax_Pure.tm_iname in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (253))
                                          (Prims.of_int (19))
                                          (Prims.of_int (253))
                                          (Prims.of_int (46)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (252))
                                          (Prims.of_int (56))
                                          (Prims.of_int (481))
                                          (Prims.of_int (57)))))
                                 (Obj.magic uu___2)
                                 (fun uu___3 ->
                                    (fun uu___3 ->
                                       match uu___3 with
                                       | Prims.Mkdtuple2 (i1, uu___4) ->
                                           let uu___5 =
                                             Obj.magic
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___6 ->
                                                     Pulse_RuntimeUtils.range_of_term
                                                       i1)) in
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.WithInv.fst"
                                                         (Prims.of_int (254))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (254))
                                                         (Prims.of_int (50)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.WithInv.fst"
                                                         (Prims.of_int (254))
                                                         (Prims.of_int (53))
                                                         (Prims.of_int (481))
                                                         (Prims.of_int (57)))))
                                                (Obj.magic uu___5)
                                                (fun uu___6 ->
                                                   (fun i_range ->
                                                      let uu___6 =
                                                        find_inv g pre () i1 in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (33)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                           (Obj.magic uu___6)
                                                           (fun uu___7 ->
                                                              (fun res ->
                                                                 let uu___7 =
                                                                   if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    res
                                                                   then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    i1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Cannot find invariant resource for iname ")
                                                                    uu___12)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    pre in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    " in the precondition ")
                                                                    uu___14)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___11
                                                                    uu___13))))
                                                                    uu___11) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    [uu___10])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    i_range)
                                                                    uu___9))
                                                                    uu___9)))
                                                                   else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ()))) in
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> res)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p,
                                                                    pre_frame,
                                                                    uu___11,
                                                                    pre_frame_typing,
                                                                    d_pre_frame_eq))
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    match 
                                                                    (returns_inv,
                                                                    post_hint)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.Some
                                                                    post) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    -> post)))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    (b, post,
                                                                    opens),
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___13
                                                                    =
                                                                    Pulse_Checker_Base.intro_post_hint
                                                                    g
                                                                    (Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                                                                    {
                                                                    Pulse_Syntax_Base.opens2
                                                                    = opens
                                                                    })
                                                                    (FStar_Pervasives_Native.Some
                                                                    (b.Pulse_Syntax_Base.binder_ty))
                                                                    post in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (12)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (100)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    post_hint1
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g
                                                                    post_hint1.Pulse_Typing.x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    post_hint1.Pulse_Typing.ret_ty)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (100)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun g_x
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    withinv_post
                                                                    g_x p i1
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    post_hint1.Pulse_Typing.post
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    post_hint1.Pulse_Typing.x))
                                                                    () () () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (100)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun res1
                                                                    ->
                                                                    match res1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    (Pulse_Syntax_Pure.tm_later
                                                                    p) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Cannot find invariant")
                                                                    uu___20)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___19
                                                                    (Pulse_PP.text
                                                                    "in the with_invariants annotated postcondition."))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    [uu___18])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStarC_Reflection_V1_Builtins.range_of_term
                                                                    post))
                                                                    uu___17))
                                                                    uu___17)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (post',
                                                                    post'_typing))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    {
                                                                    Pulse_Typing.g
                                                                    =
                                                                    (post_hint1.Pulse_Typing.g);
                                                                    Pulse_Typing.effect_annot
                                                                    =
                                                                    (post_hint1.Pulse_Typing.effect_annot);
                                                                    Pulse_Typing.effect_annot_typing
                                                                    =
                                                                    (post_hint1.Pulse_Typing.effect_annot_typing);
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
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post'
                                                                    post_hint1.Pulse_Typing.x);
                                                                    Pulse_Typing.x
                                                                    =
                                                                    (post_hint1.Pulse_Typing.x);
                                                                    Pulse_Typing.post_typing_src
                                                                    = ();
                                                                    Pulse_Typing.post_typing
                                                                    = ()
                                                                    }))))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    (uu___13,
                                                                    post,
                                                                    uu___14),
                                                                    FStar_Pervasives_Native.Some
                                                                    q) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    post in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "First postcondition:")
                                                                    uu___19)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_post_hint_t
                                                                    q in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Second postcondition:")
                                                                    uu___22)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    [uu___21])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    uu___18
                                                                    ::
                                                                    uu___20))))
                                                                    uu___18) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (FStar_Pprint.doc_of_string
                                                                    "Fatal: multiple annotated postconditions on with_invariant")
                                                                    ::
                                                                    uu___17)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___16))
                                                                    uu___16)))
                                                                    | 
                                                                    (uu___13,
                                                                    uu___14)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    "Fatal: no post hint on with_invariant")) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    post_hint1
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    body.Pulse_Syntax_Base.range1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    body_range
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_later
                                                                    p)
                                                                    pre_frame)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    pre_body
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    pre_body_typing
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun x ->
                                                                    let uu___17
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    post_hint1.Pulse_Typing.ret_ty)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun g'
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    recheck g
                                                                    post_hint1.Pulse_Typing.ret_ty
                                                                    (Pulse_Syntax_Pure.tm_type
                                                                    post_hint1.Pulse_Typing.u)
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    post_hint_ret_ty_typing
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    recheck
                                                                    g'
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    post_hint1.Pulse_Typing.post
                                                                    (Pulse_Syntax_Base.ppname_default,
                                                                    x))
                                                                    Pulse_Syntax_Pure.tm_slprop
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    post_hint_post_typing
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    find_inv_post
                                                                    g x
                                                                    post_hint1.Pulse_Typing.u
                                                                    post_hint1.Pulse_Typing.ret_ty
                                                                    post_hint1.Pulse_Typing.post
                                                                    () () i1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun res1
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    res1
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    i1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Cannot find invariant resource for iname ")
                                                                    uu___26)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    post_hint1.Pulse_Typing.post in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    " in the postcondition ")
                                                                    uu___28)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___25
                                                                    uu___27))))
                                                                    uu___25) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    [uu___24])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    i_range)
                                                                    uu___23))
                                                                    uu___23)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    -> res1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p',
                                                                    post_frame,
                                                                    uu___25,
                                                                    post_frame_typing,
                                                                    d_post_frame_equiv))
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    p p')
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    p' in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    p in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___31)
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    i1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Inconsistent slprops for iname "
                                                                    (Prims.strcat
                                                                    uu___35
                                                                    " in pre ("))
                                                                    (Prims.strcat
                                                                    x1
                                                                    ") and post ("))
                                                                    (Prims.strcat
                                                                    x2 ")"))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    uu___34
                                                                    uu___32))))
                                                                    uu___32) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    uu___31
                                                                    uu___29))))
                                                                    uu___29) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    i_range)
                                                                    uu___28))
                                                                    uu___28)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_later
                                                                    p)
                                                                    post_frame)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun
                                                                    post_body
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
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
                                                                    Pulse_Syntax_Base.EffectAnnotGhost
                                                                    {
                                                                    Pulse_Syntax_Base.opens
                                                                    = opens;_}
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (opens,
                                                                    ())
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    {
                                                                    Pulse_Syntax_Base.opens1
                                                                    = opens;_}
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (opens,
                                                                    ())
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                                                                    {
                                                                    Pulse_Syntax_Base.opens2
                                                                    = opens;_}
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (opens,
                                                                    ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    match uu___30
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (opens,
                                                                    opens_typing)
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    uu___30)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___31)
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    remove_iname
                                                                    opens i1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (fun
                                                                    opens_remove_i
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    match 
                                                                    post_hint1.Pulse_Typing.effect_annot
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotSTT
                                                                    ->
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    {
                                                                    Pulse_Syntax_Base.opens1
                                                                    =
                                                                    opens_remove_i
                                                                    }
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    uu___36
                                                                    ->
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    {
                                                                    Pulse_Syntax_Base.opens1
                                                                    =
                                                                    opens_remove_i
                                                                    }
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotGhost
                                                                    uu___36
                                                                    ->
                                                                    Pulse_Syntax_Base.EffectAnnotGhost
                                                                    {
                                                                    Pulse_Syntax_Base.opens
                                                                    =
                                                                    opens_remove_i
                                                                    }
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                                                                    uu___36
                                                                    ->
                                                                    Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                                                                    {
                                                                    Pulse_Syntax_Base.opens2
                                                                    =
                                                                    opens_remove_i
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    (fun
                                                                    effect_annot
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    Obj.magic
                                                                    ())
                                                                    uu___36)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    (fun
                                                                    effect_annot_typing
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___37
                                                                    ->
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
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (fun
                                                                    post_hint_body
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "with_inv_body")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___38)
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    (fun
                                                                    ppname ->
                                                                    let uu___39
                                                                    =
                                                                    check g
                                                                    pre_body
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint_body)
                                                                    ppname
                                                                    body in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___39)
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g
                                                                    pre_body
                                                                    post_hint_body
                                                                    r ppname))
                                                                    uu___40)))
                                                                    uu___39) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___37)
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    match uu___38
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    atomic_or_ghost_with_inames_and_pre_post
                                                                    c_body
                                                                    (Pulse_Syntax_Pure.tm_add_inv
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c_body)
                                                                    i1) pre
                                                                    post_hint1.Pulse_Typing.post)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___39)
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    (fun
                                                                    c_out ->
                                                                    let uu___40
                                                                    =
                                                                    disjointness_remove_i_i
                                                                    g opens
                                                                    i1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___40)
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    (fun tok
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    c_out))
                                                                    (Pulse_Syntax_Base.Tm_WithInv
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = i1;
                                                                    Pulse_Syntax_Base.body6
                                                                    = body1;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (90)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___41)
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    (fun tm
                                                                    ->
                                                                    let uu___42
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    Pulse_Typing.T_Equiv
                                                                    (g,
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    (atomic_or_ghost_with_inames_and_pre_post
                                                                    c_body
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c_body)
                                                                    pre_frame
                                                                    post_frame)))
                                                                    (Pulse_Syntax_Base.Tm_WithInv
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = i1;
                                                                    Pulse_Syntax_Base.body6
                                                                    = body1;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })),
                                                                    (atomic_or_ghost_with_inames_and_pre_post
                                                                    c_body
                                                                    (Pulse_Syntax_Pure.tm_add_inv
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c_body)
                                                                    i1)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i1 p)
                                                                    pre_frame)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i1 p)
                                                                    post_frame)),
                                                                    c_out,
                                                                    (Pulse_Typing.T_WithInv
                                                                    (g, i1,
                                                                    p, body1,
                                                                    (atomic_or_ghost_with_inames_and_pre_post
                                                                    c_body
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c_body)
                                                                    pre_frame
                                                                    post_frame),
                                                                    (), (),
                                                                    body_typing,
                                                                    ())),
                                                                    (Pulse_Typing.ST_SLPropEquiv
                                                                    (g,
                                                                    (atomic_or_ghost_with_inames_and_pre_post
                                                                    c_body
                                                                    (Pulse_Syntax_Pure.tm_add_inv
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c_body)
                                                                    i1)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i1 p)
                                                                    pre_frame)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i1 p)
                                                                    post_frame)),
                                                                    c_out, x,
                                                                    (), (),
                                                                    (),
                                                                    (FStar_Reflection_Typing.Rel_refl
                                                                    ((Pulse_Typing.elab_env
                                                                    g),
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    (atomic_or_ghost_with_inames_and_pre_post
                                                                    c_body
                                                                    (Pulse_Syntax_Pure.tm_add_inv
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c_body)
                                                                    i1)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i1 p)
                                                                    pre_frame)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i1 p)
                                                                    post_frame))),
                                                                    FStar_Reflection_Typing.R_Eq)),
                                                                    (), ()))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (458))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (460))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___42)
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    (fun d ->
                                                                    match 
                                                                    post_hint1.Pulse_Typing.effect_annot
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotGhost
                                                                    uu___43
                                                                    ->
                                                                    let uu___44
                                                                    =
                                                                    add_remove_inverse
                                                                    g opens
                                                                    i1 () () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___44)
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    (fun tok1
                                                                    ->
                                                                    let uu___45
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    match c_out
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (add_inv,
                                                                    obs, st)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STAtomic
                                                                    (opens,
                                                                    obs, st)),
                                                                    (Pulse_Typing.STS_AtomicInvs
                                                                    (g, st,
                                                                    add_inv,
                                                                    opens,
                                                                    obs, obs,
                                                                    ())))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (add_inv,
                                                                    st) ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STGhost
                                                                    (opens,
                                                                    st)),
                                                                    (Pulse_Typing.STS_GhostInvs
                                                                    (g, st,
                                                                    add_inv,
                                                                    opens,
                                                                    ()))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___45)
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    match uu___46
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_out_opens,
                                                                    d_sub_c)
                                                                    ->
                                                                    let uu___47
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    uu___46)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___47)
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    let uu___49
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g, tm,
                                                                    c_out,
                                                                    c_out_opens,
                                                                    d,
                                                                    d_sub_c))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___49)
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (tm,
                                                                    c_out_opens,
                                                                    d1))
                                                                    res_ppname))
                                                                    uu___50)))
                                                                    uu___48)))
                                                                    uu___46)))
                                                                    uu___45))
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    uu___43
                                                                    ->
                                                                    let uu___44
                                                                    =
                                                                    add_remove_inverse
                                                                    g opens
                                                                    i1 () () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___44)
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    (fun tok1
                                                                    ->
                                                                    let uu___45
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    match c_out
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (add_inv,
                                                                    obs, st)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STAtomic
                                                                    (opens,
                                                                    obs, st)),
                                                                    (Pulse_Typing.STS_AtomicInvs
                                                                    (g, st,
                                                                    add_inv,
                                                                    opens,
                                                                    obs, obs,
                                                                    ())))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (add_inv,
                                                                    st) ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STGhost
                                                                    (opens,
                                                                    st)),
                                                                    (Pulse_Typing.STS_GhostInvs
                                                                    (g, st,
                                                                    add_inv,
                                                                    opens,
                                                                    ()))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___45)
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    match uu___46
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_out_opens,
                                                                    d_sub_c)
                                                                    ->
                                                                    let uu___47
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    uu___46)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___47)
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    let uu___49
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g, tm,
                                                                    c_out,
                                                                    c_out_opens,
                                                                    d,
                                                                    d_sub_c))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___49)
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (tm,
                                                                    c_out_opens,
                                                                    d1))
                                                                    res_ppname))
                                                                    uu___50)))
                                                                    uu___48)))
                                                                    uu___46)))
                                                                    uu___45))
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                                                                    uu___43
                                                                    ->
                                                                    let uu___44
                                                                    =
                                                                    add_remove_inverse
                                                                    g opens
                                                                    i1 () () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___44)
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    (fun tok1
                                                                    ->
                                                                    let uu___45
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    match c_out
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (add_inv,
                                                                    obs, st)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STAtomic
                                                                    (opens,
                                                                    obs, st)),
                                                                    (Pulse_Typing.STS_AtomicInvs
                                                                    (g, st,
                                                                    add_inv,
                                                                    opens,
                                                                    obs, obs,
                                                                    ())))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (add_inv,
                                                                    st) ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STGhost
                                                                    (opens,
                                                                    st)),
                                                                    (Pulse_Typing.STS_GhostInvs
                                                                    (g, st,
                                                                    add_inv,
                                                                    opens,
                                                                    ()))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (466))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___45)
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    match uu___46
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_out_opens,
                                                                    d_sub_c)
                                                                    ->
                                                                    let uu___47
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    uu___46)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___47)
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    let uu___49
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g, tm,
                                                                    c_out,
                                                                    c_out_opens,
                                                                    d,
                                                                    d_sub_c))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___49)
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (tm,
                                                                    c_out_opens,
                                                                    d1))
                                                                    res_ppname))
                                                                    uu___50)))
                                                                    uu___48)))
                                                                    uu___46)))
                                                                    uu___45))
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotSTT
                                                                    ->
                                                                    let uu___43
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g, tm,
                                                                    c_out,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_out)),
                                                                    d,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g,
                                                                    c_out))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___43)
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (tm,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_out)),
                                                                    d1))
                                                                    res_ppname))
                                                                    uu___44)))
                                                                    uu___43)))
                                                                    uu___42)))
                                                                    uu___41)))
                                                                    uu___40)))
                                                                    uu___38)))
                                                                    uu___37)))
                                                                    uu___36)))
                                                                    uu___35)))
                                                                    uu___34)))
                                                                    uu___32)))
                                                                    uu___30)))
                                                                    uu___29)))
                                                                    uu___27)))
                                                                    uu___24)))
                                                                    uu___22)))
                                                                    uu___21)))
                                                                    uu___20)))
                                                                    uu___19)))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                uu___7)))
                                                     uu___6))) uu___3)))
                       uu___1)
let (norm_and_check :
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
              fun check ->
                let uu___ =
                  Pulse_Checker_Prover.normalize_slprop_welltyped g pre () in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (494)) (Prims.of_int (43))
                           (Prims.of_int (494)) (Prims.of_int (93)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (494)) Prims.int_one
                           (Prims.of_int (496)) (Prims.of_int (64)))))
                  (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun uu___1 ->
                        match uu___1 with
                        | FStar_Pervasives.Mkdtuple3
                            (pre', pre_equiv, pre'_typing) ->
                            let uu___2 =
                              check0 g pre' () post_hint res_ppname t check in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (495))
                                          (Prims.of_int (10))
                                          (Prims.of_int (495))
                                          (Prims.of_int (64)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (496))
                                          (Prims.of_int (2))
                                          (Prims.of_int (496))
                                          (Prims.of_int (64)))))
                                 (Obj.magic uu___2)
                                 (fun r ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 ->
                                         Pulse_Checker_Base.checker_result_t_equiv_ctxt
                                           g pre' pre post_hint () r))))
                       uu___1)
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
                norm_and_check g pre () post_hint res_ppname t check1