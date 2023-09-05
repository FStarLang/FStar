open Prims
type 'a tac_showable =
  {
  show: 'a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr }
let __proj__Mktac_showable__item__show :
  'a .
    'a tac_showable ->
      'a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr
  = fun projectee -> match projectee with | { show;_} -> show
let show :
  'a .
    'a tac_showable ->
      'a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr
  = fun projectee -> match projectee with | { show = show1;_} -> show1
let (uu___12 : Prims.string tac_showable) =
  {
    show =
      (fun uu___ ->
         (fun s ->
            Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> s)))
           uu___)
  }
let (uu___14 : unit tac_showable) =
  {
    show =
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "")))
           uu___)
  }
let (uu___16 : Prims.bool tac_showable) =
  {
    show =
      (fun uu___ ->
         (fun b ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> Prims.string_of_bool b))) uu___)
  }
let (uu___18 : Prims.int tac_showable) =
  {
    show =
      (fun uu___ ->
         (fun b ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> Prims.string_of_int b))) uu___)
  }
let showable_option :
  'a . 'a tac_showable -> 'a FStar_Pervasives_Native.option tac_showable =
  fun uu___ ->
    {
      show =
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> "None")))
              | FStar_Pervasives_Native.Some v ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Show.fst"
                                   (Prims.of_int (31)) (Prims.of_int (39))
                                   (Prims.of_int (31)) (Prims.of_int (45)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "prims.fst"
                                   (Prims.of_int (590)) (Prims.of_int (19))
                                   (Prims.of_int (590)) (Prims.of_int (31)))))
                          (Obj.magic (show uu___ v))
                          (fun uu___2 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 -> Prims.strcat "Some " uu___2)))))
             uu___1)
    }
let showable_list : 'a . 'a tac_showable -> 'a Prims.list tac_showable =
  fun uu___ -> { show = (FStar_Tactics_Util.string_of_list (show uu___)) }
let (uu___28 : Pulse_Syntax_Base.ctag tac_showable) =
  {
    show =
      (fun uu___ ->
         (fun t ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> Pulse_Syntax_Printer.ctag_to_string t))) uu___)
  }
let (uu___30 : Pulse_Syntax_Base.term tac_showable) =
  { show = Pulse_Syntax_Printer.term_to_string }
let (uu___31 : Pulse_Syntax_Base.universe tac_showable) =
  {
    show =
      (fun uu___ ->
         (fun t ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> Pulse_Syntax_Printer.univ_to_string t))) uu___)
  }
let (uu___33 : Pulse_Syntax_Base.comp tac_showable) =
  { show = Pulse_Syntax_Printer.comp_to_string }
let (uu___34 : Pulse_Typing_Env.env tac_showable) =
  { show = Pulse_Typing_Env.env_to_string }
let (uu___35 : Pulse_Typing.post_hint_t tac_showable) =
  {
    show =
      (fun h ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.Show.fst" (Prims.of_int (58))
                    (Prims.of_int (6)) (Prims.of_int (63)) (Prims.of_int (7)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                    (Prims.of_int (19)) (Prims.of_int (590))
                    (Prims.of_int (31)))))
           (Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Show.fst"
                          (Prims.of_int (58)) (Prims.of_int (15))
                          (Prims.of_int (63)) (Prims.of_int (7)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                          (Prims.of_int (19)) (Prims.of_int (590))
                          (Prims.of_int (31)))))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Show.fst"
                                (Prims.of_int (58)) (Prims.of_int (15))
                                (Prims.of_int (58)) (Prims.of_int (23)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Show.fst"
                                (Prims.of_int (58)) (Prims.of_int (15))
                                (Prims.of_int (63)) (Prims.of_int (7)))))
                       (Obj.magic (show uu___34 h.Pulse_Typing.g))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Show.fst"
                                           (Prims.of_int (58))
                                           (Prims.of_int (26))
                                           (Prims.of_int (63))
                                           (Prims.of_int (7)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "prims.fst"
                                           (Prims.of_int (590))
                                           (Prims.of_int (19))
                                           (Prims.of_int (590))
                                           (Prims.of_int (31)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Show.fst"
                                                 (Prims.of_int (59))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (63))
                                                 (Prims.of_int (7)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "prims.fst"
                                                 (Prims.of_int (590))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (590))
                                                 (Prims.of_int (31)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Show.fst"
                                                       (Prims.of_int (59))
                                                       (Prims.of_int (23))
                                                       (Prims.of_int (63))
                                                       (Prims.of_int (7)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "prims.fst"
                                                       (Prims.of_int (590))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (590))
                                                       (Prims.of_int (31)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Show.fst"
                                                             (Prims.of_int (59))
                                                             (Prims.of_int (23))
                                                             (Prims.of_int (59))
                                                             (Prims.of_int (39)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Show.fst"
                                                             (Prims.of_int (59))
                                                             (Prims.of_int (23))
                                                             (Prims.of_int (63))
                                                             (Prims.of_int (7)))))
                                                    (Obj.magic
                                                       (show
                                                          (showable_option
                                                             uu___28)
                                                          h.Pulse_Typing.ctag_hint))
                                                    (fun uu___1 ->
                                                       (fun uu___1 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (7)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (show
                                                                    uu___30
                                                                    h.Pulse_Typing.ret_ty))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (show
                                                                    uu___31
                                                                    h.Pulse_Typing.u))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (show
                                                                    uu___30
                                                                    h.Pulse_Typing.post))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    uu___4
                                                                    "; }"))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "post = "
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "; "
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    uu___3
                                                                    uu___4))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "u = "
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "; "
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    uu___2
                                                                    uu___3))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "ret_ty = "
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "; "
                                                                    uu___2))))
                                                               (fun uu___2 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    uu___1
                                                                    uu___2))))
                                                         uu___1)))
                                              (fun uu___1 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      Prims.strcat
                                                        "ctag_hint = " uu___1))))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                Prims.strcat "; " uu___1))))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          Prims.strcat uu___ uu___1)))) uu___)))
                 (fun uu___ ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 -> Prims.strcat "g = " uu___))))
           (fun uu___ ->
              FStar_Tactics_Effect.lift_div_tac
                (fun uu___1 -> Prims.strcat "{" uu___)))
  }