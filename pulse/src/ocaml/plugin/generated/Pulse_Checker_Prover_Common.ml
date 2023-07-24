open Prims
type ('g, 't) vprop_typing = unit
type mk_t =
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        ((Pulse_Syntax_Base.ppname, Pulse_Syntax_Base.st_term,
           Pulse_Syntax_Base.comp, (unit, unit, unit) Pulse_Typing.st_typing)
           FStar_Pervasives.dtuple4 FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr
let rec (list_as_vprop' :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.vprop Prims.list -> Pulse_Syntax_Base.vprop)
  =
  fun vp ->
    fun fvps ->
      match fvps with
      | [] -> vp
      | hd::tl -> list_as_vprop' (Pulse_Syntax_Base.tm_star vp hd) tl
let rec (canon_right_aux :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop Prims.list ->
      (Pulse_Syntax_Base.vprop ->
         (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
        ->
        ((Pulse_Syntax_Base.vprop Prims.list,
           Pulse_Syntax_Base.vprop Prims.list, unit) FStar_Pervasives.dtuple3,
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
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.Common.fst"
                                    (Prims.of_int (32)) (Prims.of_int (7))
                                    (Prims.of_int (32)) (Prims.of_int (11)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.Common.fst"
                                    (Prims.of_int (32)) (Prims.of_int (4))
                                    (Prims.of_int (56)) (Prims.of_int (7)))))
                           (Obj.magic (f hd))
                           (fun uu___ ->
                              (fun uu___ ->
                                 if uu___
                                 then
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Common.fst"
                                                 (Prims.of_int (34))
                                                 (Prims.of_int (32))
                                                 (Prims.of_int (34))
                                                 (Prims.of_int (56)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Common.fst"
                                                 (Prims.of_int (33))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (50))
                                                 (Prims.of_int (34)))))
                                        (Obj.magic (canon_right_aux g rest f))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                match uu___1 with
                                                | FStar_Pervasives.Mkdtuple3
                                                    (vps', fvps, uu___3) ->
                                                    FStar_Pervasives.Mkdtuple3
                                                      (vps', (hd :: fvps),
                                                        ()))))
                                 else
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Common.fst"
                                                 (Prims.of_int (53))
                                                 (Prims.of_int (33))
                                                 (Prims.of_int (53))
                                                 (Prims.of_int (57)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.Common.fst"
                                                 (Prims.of_int (52))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (55))
                                                 (Prims.of_int (33)))))
                                        (Obj.magic (canon_right_aux g rest f))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                match uu___2 with
                                                | FStar_Pervasives.Mkdtuple3
                                                    (vps', pures, uu___4) ->
                                                    FStar_Pervasives.Mkdtuple3
                                                      ((hd :: vps'), pures,
                                                        ()))))) uu___))))
          uu___2 uu___1 uu___
let (canon_right :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        unit ->
          (Pulse_Syntax_Base.vprop ->
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
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.Common.fst"
                       (Prims.of_int (66)) (Prims.of_int (33))
                       (Prims.of_int (66)) (Prims.of_int (73)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.Common.fst"
                       (Prims.of_int (66)) (Prims.of_int (3))
                       (Prims.of_int (71)) (Prims.of_int (110)))))
              (Obj.magic
                 (canon_right_aux g
                    (Pulse_Typing_Combinators.vprop_as_list ctxt) f))
              (fun uu___ ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      match uu___ with
                      | FStar_Pervasives.Mkdtuple3 (vps', pures, veq) ->
                          FStar_Pervasives.Mkdtuple3
                            ((list_as_vprop'
                                (Pulse_Typing_Combinators.list_as_vprop vps')
                                pures), (),
                              (Pulse_Checker_Base.k_elab_equiv g g
                                 (Pulse_Syntax_Base.tm_star ctxt frame)
                                 (Pulse_Syntax_Base.tm_star ctxt frame)
                                 (Pulse_Syntax_Base.tm_star ctxt frame)
                                 (Pulse_Syntax_Base.tm_star
                                    (list_as_vprop'
                                       (Pulse_Typing_Combinators.list_as_vprop
                                          vps') pures) frame)
                                 (Pulse_Checker_Base.k_elab_unit g
                                    (Pulse_Syntax_Base.tm_star ctxt frame))
                                 () ()))))
let (elim_one :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop ->
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
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.Common.fst"
                                 (Prims.of_int (85)) (Prims.of_int (26))
                                 (Prims.of_int (85)) (Prims.of_int (69)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.Common.fst"
                                 (Prims.of_int (85)) (Prims.of_int (72))
                                 (Prims.of_int (108)) (Prims.of_int (40)))))
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))
                        (fun uu___ ->
                           (fun ctxt_frame_typing ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.Common.fst"
                                            (Prims.of_int (86))
                                            (Prims.of_int (10))
                                            (Prims.of_int (86))
                                            (Prims.of_int (32)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Prover.Common.fst"
                                            (Prims.of_int (86))
                                            (Prims.of_int (35))
                                            (Prims.of_int (108))
                                            (Prims.of_int (40)))))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ ->
                                         Pulse_Typing_Env.fresh
                                           (Pulse_Typing_Env.push_env g uvs)))
                                   (fun uu___ ->
                                      (fun x ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Prover.Common.fst"
                                                       (Prims.of_int (88))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (88))
                                                       (Prims.of_int (90)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Prover.Common.fst"
                                                       (Prims.of_int (108))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (108))
                                                       (Prims.of_int (40)))))
                                              (Obj.magic
                                                 (Pulse_Checker_Base.continuation_elaborator_with_bind
                                                    g
                                                    (Pulse_Syntax_Base.tm_star
                                                       ctxt frame) c1 e1
                                                    e1_typing () x))
                                              (fun k ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___ ->
                                                      FStar_Pervasives.Mkdtuple4
                                                        ((Pulse_Typing_Env.push_binding
                                                            g x nx
                                                            (Pulse_Syntax_Base.comp_res
                                                               c1)),
                                                          (Pulse_Syntax_Base.tm_star
                                                             (Pulse_Syntax_Naming.open_term_nv
                                                                (Pulse_Syntax_Base.comp_post
                                                                   c1)
                                                                (Pulse_Syntax_Base.v_as_nv
                                                                   x)) ctxt),
                                                          (),
                                                          (Pulse_Checker_Base.k_elab_equiv
                                                             g
                                                             (Pulse_Typing_Env.push_binding
                                                                g x nx
                                                                (Pulse_Syntax_Base.comp_res
                                                                   c1))
                                                             (Pulse_Syntax_Base.tm_star
                                                                (Pulse_Syntax_Base.tm_star
                                                                   ctxt frame)
                                                                p)
                                                             (Pulse_Syntax_Base.tm_star
                                                                (Pulse_Syntax_Base.tm_star
                                                                   ctxt frame)
                                                                p)
                                                             (Pulse_Syntax_Base.tm_star
                                                                (Pulse_Syntax_Naming.open_term_nv
                                                                   (Pulse_Syntax_Base.comp_post
                                                                    c1)
                                                                   (Pulse_Syntax_Base.v_as_nv
                                                                    x))
                                                                (Pulse_Syntax_Base.tm_star
                                                                   ctxt frame))
                                                             (Pulse_Syntax_Base.tm_star
                                                                (Pulse_Syntax_Base.tm_star
                                                                   (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c1)
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    x)) ctxt)
                                                                frame) k ()
                                                             ())))))) uu___)))
                             uu___)
let rec (elim_all :
  Pulse_Typing_Env.env ->
    (Pulse_Syntax_Base.vprop ->
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
                               match ctxt.Pulse_Syntax_Base.t with
                               | Pulse_Syntax_Base.Tm_Star (ctxt', p) ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Prover.Common.fst"
                                                    (Prims.of_int (123))
                                                    (Prims.of_int (9))
                                                    (Prims.of_int (123))
                                                    (Prims.of_int (89)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Prover.Common.fst"
                                                    (Prims.of_int (124))
                                                    (Prims.of_int (7))
                                                    (Prims.of_int (144))
                                                    (Prims.of_int (10)))))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___ -> ()))
                                           (fun uu___ ->
                                              (fun p_typing ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Prover.Common.fst"
                                                               (Prims.of_int (124))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (124))
                                                               (Prims.of_int (13)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Prover.Common.fst"
                                                               (Prims.of_int (124))
                                                               (Prims.of_int (7))
                                                               (Prims.of_int (144))
                                                               (Prims.of_int (10)))))
                                                      (Obj.magic (f p))
                                                      (fun uu___ ->
                                                         (fun uu___ ->
                                                            if uu___
                                                            then
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Common.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Common.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (mk g p
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Common.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Common.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (elim_one
                                                                    g ctxt'
                                                                    frame p
                                                                    () nx e1
                                                                    c1
                                                                    e1_typing
                                                                    uvs))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g',
                                                                    uu___3,
                                                                    ctxt_typing',
                                                                    k) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Common.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Common.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    k))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun k1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Common.fst"
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Common.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Checker_Base.k_elab_equiv
                                                                    g g'
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt'
                                                                    frame) p)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt' p)
                                                                    frame)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    uu___3
                                                                    frame)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    uu___3
                                                                    frame) k1
                                                                    () ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun k2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Common.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Common.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (elim_all
                                                                    g' f mk
                                                                    uu___3
                                                                    frame ()
                                                                    uvs))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (uu___6,
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
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt' p)
                                                                    frame)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    uu___3
                                                                    frame)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt''
                                                                    frame) k2
                                                                    k'))))))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___2)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (false,
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (g, ctxt,
                                                                    (),
                                                                    (Pulse_Checker_Base.k_elab_unit
                                                                    g
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt
                                                                    frame)))))))))
                                                                    uu___1)))
                                                            else
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (false,
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (g, ctxt,
                                                                    (),
                                                                    (Pulse_Checker_Base.k_elab_unit
                                                                    g
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt
                                                                    frame)))))))))
                                                           uu___))) uu___)))
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
                                                        (Pulse_Syntax_Base.tm_star
                                                           ctxt frame)))))))))
                  uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (add_elims_aux :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.vprop ->
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
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.Common.fst"
                           (Prims.of_int (158)) (Prims.of_int (40))
                           (Prims.of_int (158)) (Prims.of_int (71)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.Common.fst"
                           (Prims.of_int (158)) (Prims.of_int (4))
                           (Prims.of_int (161)) (Prims.of_int (66)))))
                  (Obj.magic (canon_right g ctxt frame () f))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | FStar_Pervasives.Mkdtuple3 (ctxt', ctxt'_typing, k)
                            ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.Common.fst"
                                          (Prims.of_int (160))
                                          (Prims.of_int (9))
                                          (Prims.of_int (160))
                                          (Prims.of_int (39)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.Common.fst"
                                          (Prims.of_int (158))
                                          (Prims.of_int (74))
                                          (Prims.of_int (161))
                                          (Prims.of_int (66)))))
                                 (Obj.magic
                                    (elim_all g f mk ctxt' frame () uvs))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         match uu___1 with
                                         | (progress,
                                            FStar_Pervasives.Mkdtuple4
                                            (g', ctxt'', ctxt''_typing, k'))
                                             ->
                                             (progress,
                                               (FStar_Pervasives.Mkdtuple4
                                                  (g', ctxt'', (),
                                                    (Pulse_Checker_Base.k_elab_trans
                                                       g g g'
                                                       (Pulse_Syntax_Base.tm_star
                                                          ctxt frame)
                                                       (Pulse_Syntax_Base.tm_star
                                                          ctxt' frame)
                                                       (Pulse_Syntax_Base.tm_star
                                                          ctxt'' frame) k k'))))))))
                       uu___)
let rec (add_elims :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.vprop ->
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
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.Common.fst"
                           (Prims.of_int (172)) (Prims.of_int (25))
                           (Prims.of_int (172)) (Prims.of_int (59)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.Common.fst"
                           (Prims.of_int (172)) (Prims.of_int (4))
                           (Prims.of_int (179)) (Prims.of_int (6)))))
                  (Obj.magic (add_elims_aux g ctxt frame f mk () uvs))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | (progress, res) ->
                            if Prims.op_Negation progress
                            then
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 -> res)))
                            else
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.Common.fst"
                                               (Prims.of_int (176))
                                               (Prims.of_int (45))
                                               (Prims.of_int (176))
                                               (Prims.of_int (48)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.Common.fst"
                                               (Prims.of_int (175))
                                               (Prims.of_int (10))
                                               (Prims.of_int (179))
                                               (Prims.of_int (6)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 -> res))
                                      (fun uu___2 ->
                                         (fun uu___2 ->
                                            match uu___2 with
                                            | FStar_Pervasives.Mkdtuple4
                                                (g', ctxt', ctxt'_typing, k)
                                                ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.Common.fst"
                                                              (Prims.of_int (177))
                                                              (Prims.of_int (49))
                                                              (Prims.of_int (177))
                                                              (Prims.of_int (80)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.Common.fst"
                                                              (Prims.of_int (176))
                                                              (Prims.of_int (51))
                                                              (Prims.of_int (178))
                                                              (Prims.of_int (57)))))
                                                     (Obj.magic
                                                        (add_elims g' ctxt'
                                                           frame f mk () uvs))
                                                     (fun uu___3 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             match uu___3
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
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt
                                                                    frame)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt'
                                                                    frame)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt''
                                                                    frame) k
                                                                    k'))))))
                                           uu___2)))) uu___)
type preamble =
  {
  g0: Pulse_Typing_Env.env ;
  ctxt: Pulse_Syntax_Base.vprop ;
  frame: Pulse_Syntax_Base.vprop ;
  ctxt_frame_typing: unit ;
  goals: Pulse_Syntax_Base.vprop }
let (__proj__Mkpreamble__item__g0 : preamble -> Pulse_Typing_Env.env) =
  fun projectee ->
    match projectee with
    | { g0; ctxt; frame; ctxt_frame_typing; goals;_} -> g0
let (__proj__Mkpreamble__item__ctxt : preamble -> Pulse_Syntax_Base.vprop) =
  fun projectee ->
    match projectee with
    | { g0; ctxt; frame; ctxt_frame_typing; goals;_} -> ctxt
let (__proj__Mkpreamble__item__frame : preamble -> Pulse_Syntax_Base.vprop) =
  fun projectee ->
    match projectee with
    | { g0; ctxt; frame; ctxt_frame_typing; goals;_} -> frame

let (__proj__Mkpreamble__item__goals : preamble -> Pulse_Syntax_Base.vprop) =
  fun projectee ->
    match projectee with
    | { g0; ctxt; frame; ctxt_frame_typing; goals;_} -> goals
let (op_Array_Access :
  Pulse_Checker_Prover_Substs.ss_t ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  = fun ss -> fun t -> Pulse_Checker_Prover_Substs.ss_term t ss
let (op_Star :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.vprop -> Pulse_Syntax_Base.term)
  = Pulse_Syntax_Base.tm_star
type 'preamble1 prover_state =
  {
  pg: Pulse_Typing_Env.env ;
  remaining_ctxt: Pulse_Syntax_Base.vprop Prims.list ;
  remaining_ctxt_frame_typing: unit ;
  uvs: Pulse_Typing_Env.env ;
  ss: Pulse_Checker_Prover_Substs.ss_t ;
  solved: Pulse_Syntax_Base.vprop ;
  unsolved: Pulse_Syntax_Base.vprop Prims.list ;
  k: (unit, unit, unit, unit) Pulse_Checker_Base.continuation_elaborator ;
  goals_inv: unit ;
  solved_inv: unit }
let (__proj__Mkprover_state__item__pg :
  preamble -> unit prover_state -> Pulse_Typing_Env.env) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; k; goals_inv; solved_inv;_} -> pg
let (__proj__Mkprover_state__item__remaining_ctxt :
  preamble -> unit prover_state -> Pulse_Syntax_Base.vprop Prims.list) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; k; goals_inv; solved_inv;_} -> remaining_ctxt

let (__proj__Mkprover_state__item__uvs :
  preamble -> unit prover_state -> Pulse_Typing_Env.env) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; k; goals_inv; solved_inv;_} -> uvs
let (__proj__Mkprover_state__item__ss :
  preamble -> unit prover_state -> Pulse_Checker_Prover_Substs.ss_t) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; k; goals_inv; solved_inv;_} -> ss
let (__proj__Mkprover_state__item__solved :
  preamble -> unit prover_state -> Pulse_Syntax_Base.vprop) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; k; goals_inv; solved_inv;_} -> solved
let (__proj__Mkprover_state__item__unsolved :
  preamble -> unit prover_state -> Pulse_Syntax_Base.vprop Prims.list) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; k; goals_inv; solved_inv;_} -> unsolved
let (__proj__Mkprover_state__item__k :
  preamble ->
    unit prover_state ->
      (unit, unit, unit, unit) Pulse_Checker_Base.continuation_elaborator)
  =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; k; goals_inv; solved_inv;_} -> k
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
let (st_typing_subst :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp_st ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Checker_Prover_Substs.ss_t ->
              ((unit, unit, unit) Pulse_Typing.st_typing
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun uvs ->
      fun t ->
        fun c ->
          fun d ->
            fun ss ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.Prover.Common.fsti"
                         (Prims.of_int (105)) (Prims.of_int (16))
                         (Prims.of_int (105)) (Prims.of_int (43)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.Prover.Common.fsti"
                         (Prims.of_int (106)) (Prims.of_int (2))
                         (Prims.of_int (113)) (Prims.of_int (10)))))
                (Obj.magic
                   (Pulse_Checker_Prover_Substs.ss_to_nt_substs g uvs ss))
                (fun nts_opt ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        match nts_opt with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some nts ->
                            FStar_Pervasives_Native.Some
                              (Pulse_Checker_Prover_Substs.st_typing_nt_substs
                                 g uvs
                                 (Pulse_Typing_Env.mk_env
                                    (Pulse_Typing_Env.fstar_env g)) t c d nts)))
let (st_typing_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Typing_Env.env -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun g' ->
      fun t ->
        fun c ->
          fun d ->
            fun g1 ->
              let g2 = Pulse_Typing_Env.diff g1 g in
              let d1 =
                Pulse_Typing_Metatheory.st_typing_weakening g g' t c d g2 in
              d1
let (st_typing_weakening_standard :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Typing_Env.env -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t ->
      fun c ->
        fun d ->
          fun g1 ->
            let g' = Pulse_Typing_Env.mk_env (Pulse_Typing_Env.fstar_env g) in
            let d1 = st_typing_weakening g g' t c d g1 in d1
let (st_typing_weakening_end :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Typing_Env.env -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun g' ->
      fun t ->
        fun c ->
          fun d ->
            fun g'' ->
              let g2 = Pulse_Typing_Env.diff g'' g' in
              let emp_env =
                Pulse_Typing_Env.mk_env (Pulse_Typing_Env.fstar_env g) in
              let d1 =
                Pulse_Typing_Metatheory.st_typing_weakening
                  (Pulse_Typing_Env.push_env g g') emp_env t c
                  (FStar_Pervasives.coerce_eq () d) g2 in
              FStar_Pervasives.coerce_eq () d1
type ('ss1, 'ss2) ss_extends = unit
type ('preamble1, 'pst1, 'pst2) pst_extends = unit
type prover_t =
  preamble ->
    unit prover_state ->
      (unit prover_state, unit) FStar_Tactics_Effect.tac_repr
let (debug_prover :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun s ->
           if
             Pulse_RuntimeUtils.debug_at_level (Pulse_Typing_Env.fstar_env g)
               "prover"
           then
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.Common.fsti"
                              (Prims.of_int (187)) (Prims.of_int (15))
                              (Prims.of_int (187)) (Prims.of_int (21)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.Common.fsti"
                              (Prims.of_int (187)) (Prims.of_int (7))
                              (Prims.of_int (187)) (Prims.of_int (21)))))
                     (Obj.magic (s ()))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic (FStar_Tactics_V1_Builtins.print uu___))
                          uu___)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___