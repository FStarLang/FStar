open Prims
type ('g, 't) slprop_typing = unit
type mk_t =
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.slprop ->
      unit ->
        ((Pulse_Syntax_Base.ppname, Pulse_Syntax_Base.st_term,
           Pulse_Syntax_Base.comp, (unit, unit, unit) Pulse_Typing.st_typing)
           FStar_Pervasives.dtuple4 FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr
let rec (list_as_slprop' :
  Pulse_Syntax_Base.slprop ->
    Pulse_Syntax_Base.slprop Prims.list -> Pulse_Syntax_Base.slprop)
  =
  fun vp ->
    fun fvps ->
      match fvps with
      | [] -> vp
      | hd::tl -> list_as_slprop' (Pulse_Syntax_Pure.tm_star vp hd) tl
let rec (canon_right_aux :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.slprop Prims.list ->
      (Pulse_Syntax_Base.slprop ->
         (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
        ->
        ((Pulse_Syntax_Base.slprop Prims.list,
           Pulse_Syntax_Base.slprop Prims.list, unit)
           FStar_Pervasives.dtuple3,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun vps ->
             fun f ->
               match vps with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ ->
                              FStar_Pervasives.Mkdtuple3 ([], [], ()))))
               | hd::rest ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = f hd in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.Base.fst"
                                    (Prims.of_int (41)) (Prims.of_int (7))
                                    (Prims.of_int (41)) (Prims.of_int (11)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.Base.fst"
                                    (Prims.of_int (41)) (Prims.of_int (4))
                                    (Prims.of_int (65)) (Prims.of_int (7)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 if uu___1
                                 then
                                   let uu___2 = canon_right_aux g rest f in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Base.fst"
                                                 (Prims.of_int (43))
                                                 (Prims.of_int (32))
                                                 (Prims.of_int (43))
                                                 (Prims.of_int (56)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Base.fst"
                                                 (Prims.of_int (42))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (59))
                                                 (Prims.of_int (34)))))
                                        (Obj.magic uu___2)
                                        (fun uu___3 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___4 ->
                                                match uu___3 with
                                                | FStar_Pervasives.Mkdtuple3
                                                    (vps', fvps, uu___5) ->
                                                    FStar_Pervasives.Mkdtuple3
                                                      (vps', (hd :: fvps),
                                                        ()))))
                                 else
                                   (let uu___3 = canon_right_aux g rest f in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.Base.fst"
                                                  (Prims.of_int (62))
                                                  (Prims.of_int (33))
                                                  (Prims.of_int (62))
                                                  (Prims.of_int (57)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Prover.Base.fst"
                                                  (Prims.of_int (61))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (64))
                                                  (Prims.of_int (33)))))
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___5 ->
                                                 match uu___4 with
                                                 | FStar_Pervasives.Mkdtuple3
                                                     (vps', pures, uu___6) ->
                                                     FStar_Pervasives.Mkdtuple3
                                                       ((hd :: vps'), pures,
                                                         ())))))) uu___1))))
          uu___2 uu___1 uu___
let (canon_right :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        unit ->
          (Pulse_Syntax_Base.slprop ->
             (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
            ->
            ((Pulse_Syntax_Base.term, unit,
               (unit, unit, unit, unit)
                 Pulse_Checker_Base.continuation_elaborator)
               FStar_Pervasives.dtuple3,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun frame ->
        fun ctxt_frame_typing ->
          fun f ->
            let uu___ =
              canon_right_aux g (Pulse_Syntax_Pure.slprop_as_list ctxt) f in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.Base.fst"
                       (Prims.of_int (75)) (Prims.of_int (33))
                       (Prims.of_int (75)) (Prims.of_int (74)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.Base.fst"
                       (Prims.of_int (75)) (Prims.of_int (3))
                       (Prims.of_int (80)) (Prims.of_int (111)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      match uu___1 with
                      | FStar_Pervasives.Mkdtuple3 (vps', pures, veq) ->
                          FStar_Pervasives.Mkdtuple3
                            ((list_as_slprop'
                                (Pulse_Syntax_Pure.list_as_slprop vps') pures),
                              (),
                              (Pulse_Checker_Base.k_elab_equiv g g
                                 (Pulse_Syntax_Pure.tm_star ctxt frame)
                                 (Pulse_Syntax_Pure.tm_star ctxt frame)
                                 (Pulse_Syntax_Pure.tm_star ctxt frame)
                                 (Pulse_Syntax_Pure.tm_star
                                    (list_as_slprop'
                                       (Pulse_Syntax_Pure.list_as_slprop vps')
                                       pures) frame)
                                 (Pulse_Checker_Base.k_elab_unit g
                                    (Pulse_Syntax_Pure.tm_star ctxt frame))
                                 () ()))))
let (elim_one :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.slprop ->
        Pulse_Syntax_Base.slprop ->
          unit ->
            Pulse_Syntax_Base.ppname ->
              Pulse_Syntax_Base.st_term ->
                Pulse_Syntax_Base.comp ->
                  (unit, unit, unit) Pulse_Typing.st_typing ->
                    Pulse_Typing_Env.env ->
                      ((Pulse_Typing_Env.env, Pulse_Syntax_Base.term, 
                         unit,
                         (unit, unit, unit, unit)
                           Pulse_Checker_Base.continuation_elaborator)
                         FStar_Pervasives.dtuple4,
                        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun frame ->
        fun p ->
          fun ctxt_frame_p_typing ->
            fun nx ->
              fun e1 ->
                fun c1 ->
                  fun e1_typing ->
                    fun uvs ->
                      let uu___ =
                        Obj.magic
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 -> ())) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.Base.fst"
                                 (Prims.of_int (94)) (Prims.of_int (26))
                                 (Prims.of_int (94)) (Prims.of_int (69)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.Base.fst"
                                 (Prims.of_int (94)) (Prims.of_int (72))
                                 (Prims.of_int (117)) (Prims.of_int (40)))))
                        (Obj.magic uu___)
                        (fun uu___1 ->
                           (fun ctxt_frame_typing ->
                              let uu___1 =
                                Obj.magic
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 ->
                                        Pulse_Typing_Env.fresh
                                          (Pulse_Typing_Env.push_env g uvs))) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.Base.fst"
                                            (Prims.of_int (95))
                                            (Prims.of_int (10))
                                            (Prims.of_int (95))
                                            (Prims.of_int (32)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.Base.fst"
                                            (Prims.of_int (95))
                                            (Prims.of_int (35))
                                            (Prims.of_int (117))
                                            (Prims.of_int (40)))))
                                   (Obj.magic uu___1)
                                   (fun uu___2 ->
                                      (fun x ->
                                         let uu___2 =
                                           Pulse_Checker_Base.continuation_elaborator_with_bind
                                             g
                                             (Pulse_Syntax_Pure.tm_star ctxt
                                                frame) c1 e1 e1_typing ()
                                             (nx, x) in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Prover.Base.fst"
                                                       (Prims.of_int (97))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (97))
                                                       (Prims.of_int (96)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Prover.Base.fst"
                                                       (Prims.of_int (117))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (117))
                                                       (Prims.of_int (40)))))
                                              (Obj.magic uu___2)
                                              (fun k ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___3 ->
                                                      FStar_Pervasives.Mkdtuple4
                                                        ((Pulse_Typing_Env.push_binding
                                                            g x nx
                                                            (Pulse_Syntax_Base.comp_res
                                                               c1)),
                                                          (Pulse_Syntax_Pure.tm_star
                                                             (Pulse_Syntax_Naming.open_term_nv
                                                                (Pulse_Syntax_Base.comp_post
                                                                   c1)
                                                                (nx, x)) ctxt),
                                                          (),
                                                          (Pulse_Checker_Base.k_elab_equiv
                                                             g
                                                             (Pulse_Typing_Env.push_binding
                                                                g x nx
                                                                (Pulse_Syntax_Base.comp_res
                                                                   c1))
                                                             (Pulse_Syntax_Pure.tm_star
                                                                (Pulse_Syntax_Pure.tm_star
                                                                   ctxt frame)
                                                                p)
                                                             (Pulse_Syntax_Pure.tm_star
                                                                (Pulse_Syntax_Pure.tm_star
                                                                   ctxt frame)
                                                                p)
                                                             (Pulse_Syntax_Pure.tm_star
                                                                (Pulse_Syntax_Naming.open_term_nv
                                                                   (Pulse_Syntax_Base.comp_post
                                                                    c1)
                                                                   (nx, x))
                                                                (Pulse_Syntax_Pure.tm_star
                                                                   ctxt frame))
                                                             (Pulse_Syntax_Pure.tm_star
                                                                (Pulse_Syntax_Pure.tm_star
                                                                   (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c1)
                                                                    (nx, x))
                                                                   ctxt)
                                                                frame) k ()
                                                             ())))))) uu___2)))
                             uu___1)
let rec (elim_all :
  Pulse_Typing_Env.env ->
    (Pulse_Syntax_Base.slprop ->
       (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
      ->
      mk_t ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Typing_Env.env ->
                ((Prims.bool * (Pulse_Typing_Env.env, Pulse_Syntax_Base.term,
                   unit,
                   (unit, unit, unit, unit)
                     Pulse_Checker_Base.continuation_elaborator)
                   FStar_Pervasives.dtuple4),
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
                   fun f ->
                     fun mk ->
                       fun ctxt ->
                         fun frame ->
                           fun ctxt_frame_typing ->
                             fun uvs ->
                               match Pulse_Syntax_Pure.inspect_term ctxt with
                               | Pulse_Syntax_Pure.Tm_Star (ctxt', p) ->
                                   Obj.magic
                                     (Obj.repr
                                        (let uu___ =
                                           Obj.magic
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 -> ())) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Prover.Base.fst"
                                                    (Prims.of_int (132))
                                                    (Prims.of_int (9))
                                                    (Prims.of_int (132))
                                                    (Prims.of_int (89)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Prover.Base.fst"
                                                    (Prims.of_int (133))
                                                    (Prims.of_int (7))
                                                    (Prims.of_int (153))
                                                    (Prims.of_int (10)))))
                                           (Obj.magic uu___)
                                           (fun uu___1 ->
                                              (fun p_typing ->
                                                 let uu___1 = f p in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Prover.Base.fst"
                                                               (Prims.of_int (133))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (133))
                                                               (Prims.of_int (13)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Prover.Base.fst"
                                                               (Prims.of_int (133))
                                                               (Prims.of_int (7))
                                                               (Prims.of_int (153))
                                                               (Prims.of_int (10)))))
                                                      (Obj.magic uu___1)
                                                      (fun uu___2 ->
                                                         (fun uu___2 ->
                                                            if uu___2
                                                            then
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (let uu___3
                                                                    =
                                                                    mk g p () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Base.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Base.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    uu___3)
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (nx, e1,
                                                                    c1,
                                                                    e1_typing))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___5
                                                                    =
                                                                    elim_one
                                                                    g ctxt'
                                                                    frame p
                                                                    () nx e1
                                                                    c1
                                                                    e1_typing
                                                                    uvs in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Base.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Base.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g',
                                                                    uu___7,
                                                                    ctxt_typing',
                                                                    k) ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    k)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Base.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Base.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun k1
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Checker_Base.k_elab_equiv
                                                                    g g'
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    ctxt'
                                                                    frame) p)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    ctxt' p)
                                                                    frame)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    uu___7
                                                                    frame)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    uu___7
                                                                    frame) k1
                                                                    () ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Base.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Base.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun k2
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    elim_all
                                                                    g' f mk
                                                                    uu___7
                                                                    frame ()
                                                                    uvs in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Base.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Base.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (uu___13,
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g'',
                                                                    ctxt'',
                                                                    ctxt_typing'',
                                                                    k')) ->
                                                                    (true,
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (g'',
                                                                    ctxt'',
                                                                    (),
                                                                    (Pulse_Checker_Base.k_elab_trans
                                                                    g g' g''
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    ctxt' p)
                                                                    frame)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    uu___7
                                                                    frame)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    ctxt''
                                                                    frame) k2
                                                                    k'))))))))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___6)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (false,
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (g, ctxt,
                                                                    (),
                                                                    (Pulse_Checker_Base.k_elab_unit
                                                                    g
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    ctxt
                                                                    frame)))))))))
                                                                    uu___4)))
                                                            else
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (false,
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (g, ctxt,
                                                                    (),
                                                                    (Pulse_Checker_Base.k_elab_unit
                                                                    g
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    ctxt
                                                                    frame)))))))))
                                                           uu___2))) uu___1)))
                               | uu___ ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              (false,
                                                (FStar_Pervasives.Mkdtuple4
                                                   (g, ctxt, (),
                                                     (Pulse_Checker_Base.k_elab_unit
                                                        g
                                                        (Pulse_Syntax_Pure.tm_star
                                                           ctxt frame)))))))))
                  uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (add_elims_aux :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.slprop ->
           (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
          ->
          mk_t ->
            unit ->
              Pulse_Typing_Env.env ->
                ((Prims.bool * (Pulse_Typing_Env.env, Pulse_Syntax_Base.term,
                   unit,
                   (unit, unit, unit, unit)
                     Pulse_Checker_Base.continuation_elaborator)
                   FStar_Pervasives.dtuple4),
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun frame ->
        fun f ->
          fun mk ->
            fun ctxt_frame_typing ->
              fun uvs ->
                let uu___ = canon_right g ctxt frame () f in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Prover.Base.fst"
                           (Prims.of_int (167)) (Prims.of_int (40))
                           (Prims.of_int (167)) (Prims.of_int (71)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Prover.Base.fst"
                           (Prims.of_int (167)) (Prims.of_int (4))
                           (Prims.of_int (170)) (Prims.of_int (66)))))
                  (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun uu___1 ->
                        match uu___1 with
                        | FStar_Pervasives.Mkdtuple3 (ctxt', ctxt'_typing, k)
                            ->
                            let uu___2 = elim_all g f mk ctxt' frame () uvs in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.Base.fst"
                                          (Prims.of_int (169))
                                          (Prims.of_int (9))
                                          (Prims.of_int (169))
                                          (Prims.of_int (39)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.Base.fst"
                                          (Prims.of_int (167))
                                          (Prims.of_int (74))
                                          (Prims.of_int (170))
                                          (Prims.of_int (66)))))
                                 (Obj.magic uu___2)
                                 (fun uu___3 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___4 ->
                                         match uu___3 with
                                         | (progress,
                                            FStar_Pervasives.Mkdtuple4
                                            (g', ctxt'', ctxt''_typing, k'))
                                             ->
                                             (progress,
                                               (FStar_Pervasives.Mkdtuple4
                                                  (g', ctxt'', (),
                                                    (Pulse_Checker_Base.k_elab_trans
                                                       g g g'
                                                       (Pulse_Syntax_Pure.tm_star
                                                          ctxt frame)
                                                       (Pulse_Syntax_Pure.tm_star
                                                          ctxt' frame)
                                                       (Pulse_Syntax_Pure.tm_star
                                                          ctxt'' frame) k k'))))))))
                       uu___1)
let rec (add_elims :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.slprop ->
           (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
          ->
          mk_t ->
            unit ->
              Pulse_Typing_Env.env ->
                ((Pulse_Typing_Env.env, Pulse_Syntax_Base.term, unit,
                   (unit, unit, unit, unit)
                     Pulse_Checker_Base.continuation_elaborator)
                   FStar_Pervasives.dtuple4,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun frame ->
        fun f ->
          fun mk ->
            fun ctxt_typing ->
              fun uvs ->
                let uu___ = add_elims_aux g ctxt frame f mk () uvs in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Prover.Base.fst"
                           (Prims.of_int (181)) (Prims.of_int (25))
                           (Prims.of_int (181)) (Prims.of_int (59)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Prover.Base.fst"
                           (Prims.of_int (181)) (Prims.of_int (4))
                           (Prims.of_int (188)) (Prims.of_int (6)))))
                  (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun uu___1 ->
                        match uu___1 with
                        | (progress, res) ->
                            if Prims.op_Negation progress
                            then
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 -> res)))
                            else
                              Obj.magic
                                (Obj.repr
                                   (let uu___3 =
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 -> res)) in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.Base.fst"
                                               (Prims.of_int (185))
                                               (Prims.of_int (45))
                                               (Prims.of_int (185))
                                               (Prims.of_int (48)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.Base.fst"
                                               (Prims.of_int (184))
                                               (Prims.of_int (10))
                                               (Prims.of_int (188))
                                               (Prims.of_int (6)))))
                                      (Obj.magic uu___3)
                                      (fun uu___4 ->
                                         (fun uu___4 ->
                                            match uu___4 with
                                            | FStar_Pervasives.Mkdtuple4
                                                (g', ctxt', ctxt'_typing, k)
                                                ->
                                                let uu___5 =
                                                  add_elims g' ctxt' frame f
                                                    mk () uvs in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.Base.fst"
                                                              (Prims.of_int (186))
                                                              (Prims.of_int (49))
                                                              (Prims.of_int (186))
                                                              (Prims.of_int (80)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.Base.fst"
                                                              (Prims.of_int (185))
                                                              (Prims.of_int (51))
                                                              (Prims.of_int (187))
                                                              (Prims.of_int (57)))))
                                                     (Obj.magic uu___5)
                                                     (fun uu___6 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___7 ->
                                                             match uu___6
                                                             with
                                                             | FStar_Pervasives.Mkdtuple4
                                                                 (g'',
                                                                  ctxt'',
                                                                  ctxt''_typing,
                                                                  k')
                                                                 ->
                                                                 FStar_Pervasives.Mkdtuple4
                                                                   (g'',
                                                                    ctxt'',
                                                                    (),
                                                                    (Pulse_Checker_Base.k_elab_trans
                                                                    g g' g''
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    ctxt
                                                                    frame)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    ctxt'
                                                                    frame)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    ctxt''
                                                                    frame) k
                                                                    k'))))))
                                           uu___4)))) uu___1)
type preamble =
  {
  g0: Pulse_Typing_Env.env ;
  ctxt: Pulse_Syntax_Base.slprop ;
  frame: Pulse_Syntax_Base.slprop ;
  ctxt_frame_typing: unit ;
  goals: Pulse_Syntax_Base.slprop }
let (__proj__Mkpreamble__item__g0 : preamble -> Pulse_Typing_Env.env) =
  fun projectee ->
    match projectee with
    | { g0; ctxt; frame; ctxt_frame_typing; goals;_} -> g0
let (__proj__Mkpreamble__item__ctxt : preamble -> Pulse_Syntax_Base.slprop) =
  fun projectee ->
    match projectee with
    | { g0; ctxt; frame; ctxt_frame_typing; goals;_} -> ctxt
let (__proj__Mkpreamble__item__frame : preamble -> Pulse_Syntax_Base.slprop)
  =
  fun projectee ->
    match projectee with
    | { g0; ctxt; frame; ctxt_frame_typing; goals;_} -> frame

let (__proj__Mkpreamble__item__goals : preamble -> Pulse_Syntax_Base.slprop)
  =
  fun projectee ->
    match projectee with
    | { g0; ctxt; frame; ctxt_frame_typing; goals;_} -> goals
let (op_Array_Access :
  Pulse_Checker_Prover_Substs.ss_t ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  = fun ss -> fun t -> Pulse_Checker_Prover_Substs.ss_term t ss
let (op_Star :
  Pulse_Syntax_Base.slprop ->
    Pulse_Syntax_Base.slprop -> Pulse_Syntax_Base.term)
  = Pulse_Syntax_Pure.tm_star
type 'preamble1 prover_state =
  {
  pg: Pulse_Typing_Env.env ;
  remaining_ctxt: Pulse_Syntax_Base.slprop Prims.list ;
  remaining_ctxt_frame_typing: unit ;
  uvs: Pulse_Typing_Env.env ;
  ss: Pulse_Checker_Prover_Substs.ss_t ;
  nts:
    (Pulse_Checker_Prover_Substs.nt_substs,
      FStarC_TypeChecker_Core.tot_or_ghost Prims.list) Prims.dtuple2
      FStar_Pervasives_Native.option
    ;
  solved: Pulse_Syntax_Base.slprop ;
  unsolved: Pulse_Syntax_Base.slprop Prims.list ;
  k: (unit, unit, unit, unit) Pulse_Checker_Base.continuation_elaborator ;
  goals_inv: unit ;
  solved_inv: unit ;
  progress: Prims.bool ;
  allow_ambiguous: Prims.bool }
let (__proj__Mkprover_state__item__pg :
  preamble -> unit prover_state -> Pulse_Typing_Env.env) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; nts;
          solved; unsolved; k; goals_inv; solved_inv; progress;
          allow_ambiguous;_} -> pg
let (__proj__Mkprover_state__item__remaining_ctxt :
  preamble -> unit prover_state -> Pulse_Syntax_Base.slprop Prims.list) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; nts;
          solved; unsolved; k; goals_inv; solved_inv; progress;
          allow_ambiguous;_} -> remaining_ctxt

let (__proj__Mkprover_state__item__uvs :
  preamble -> unit prover_state -> Pulse_Typing_Env.env) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; nts;
          solved; unsolved; k; goals_inv; solved_inv; progress;
          allow_ambiguous;_} -> uvs
let (__proj__Mkprover_state__item__ss :
  preamble -> unit prover_state -> Pulse_Checker_Prover_Substs.ss_t) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; nts;
          solved; unsolved; k; goals_inv; solved_inv; progress;
          allow_ambiguous;_} -> ss
let (__proj__Mkprover_state__item__nts :
  preamble ->
    unit prover_state ->
      (Pulse_Checker_Prover_Substs.nt_substs,
        FStarC_TypeChecker_Core.tot_or_ghost Prims.list) Prims.dtuple2
        FStar_Pervasives_Native.option)
  =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; nts;
          solved; unsolved; k; goals_inv; solved_inv; progress;
          allow_ambiguous;_} -> nts
let (__proj__Mkprover_state__item__solved :
  preamble -> unit prover_state -> Pulse_Syntax_Base.slprop) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; nts;
          solved; unsolved; k; goals_inv; solved_inv; progress;
          allow_ambiguous;_} -> solved
let (__proj__Mkprover_state__item__unsolved :
  preamble -> unit prover_state -> Pulse_Syntax_Base.slprop Prims.list) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; nts;
          solved; unsolved; k; goals_inv; solved_inv; progress;
          allow_ambiguous;_} -> unsolved
let (__proj__Mkprover_state__item__k :
  preamble ->
    unit prover_state ->
      (unit, unit, unit, unit) Pulse_Checker_Base.continuation_elaborator)
  =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; nts;
          solved; unsolved; k; goals_inv; solved_inv; progress;
          allow_ambiguous;_} -> k
let (__proj__Mkprover_state__item__progress :
  preamble -> unit prover_state -> Prims.bool) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; nts;
          solved; unsolved; k; goals_inv; solved_inv; progress;
          allow_ambiguous;_} -> progress
let (__proj__Mkprover_state__item__allow_ambiguous :
  preamble -> unit prover_state -> Prims.bool) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; nts;
          solved; unsolved; k; goals_inv; solved_inv; progress;
          allow_ambiguous;_} -> allow_ambiguous
type ('preamble1, 'st) is_terminal = unit
let (extend_post_hint_opt_g :
  Pulse_Typing_Env.env ->
    unit Pulse_Typing.post_hint_opt ->
      Pulse_Typing_Env.env -> unit Pulse_Typing.post_hint_opt)
  =
  fun g ->
    fun post_hint ->
      fun g1 ->
        match post_hint with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some post_hint1 ->
            FStar_Pervasives_Native.Some post_hint1
type ('ss1, 'ss2) ss_extends = unit
type ('preamble1, 'preamble2, 'pst1, 'pst2) pst_extends = unit
type prover_t =
  preamble ->
    unit prover_state ->
      (unit prover_state, unit) FStar_Tactics_Effect.tac_repr