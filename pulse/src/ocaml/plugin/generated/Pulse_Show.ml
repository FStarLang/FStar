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
let (tac_showable_string : Prims.string tac_showable) =
  {
    show =
      (fun uu___ ->
         (fun s ->
            Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> s)))
           uu___)
  }
let (tac_showable_unit : unit tac_showable) =
  {
    show =
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "()"))) uu___)
  }
let (tac_showable_bool : Prims.bool tac_showable) =
  {
    show =
      (fun uu___ ->
         (fun b ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> Prims.string_of_bool b))) uu___)
  }
let (tac_showable_int : Prims.int tac_showable) =
  {
    show =
      (fun uu___ ->
         (fun b ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> Prims.string_of_int b))) uu___)
  }
let tac_showable_option :
  'a . 'a tac_showable -> 'a FStar_Pervasives_Native.option tac_showable =
  fun tac_showable_a ->
    {
      show =
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> "None")))
              | FStar_Pervasives_Native.Some v ->
                  Obj.magic
                    (Obj.repr
                       (let uu___1 = show tac_showable_a v in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Show.fst"
                                   (Prims.of_int (43)) (Prims.of_int (39))
                                   (Prims.of_int (43)) (Prims.of_int (45)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "prims.fst"
                                   (Prims.of_int (611)) (Prims.of_int (19))
                                   (Prims.of_int (611)) (Prims.of_int (31)))))
                          (Obj.magic uu___1)
                          (fun uu___2 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 -> Prims.strcat "Some " uu___2)))))
             uu___)
    }
let tac_showable_list : 'a . 'a tac_showable -> 'a Prims.list tac_showable =
  fun tac_showable_a ->
    { show = (FStar_Tactics_Util.string_of_list (show tac_showable_a)) }
let (tac_showable_ctag : Pulse_Syntax_Base.ctag tac_showable) =
  {
    show =
      (fun uu___ ->
         (fun t ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> Pulse_Syntax_Printer.ctag_to_string t))) uu___)
  }
let (tac_showable_term : Pulse_Syntax_Base.term tac_showable) =
  { show = Pulse_Syntax_Printer.term_to_string }
let (tac_showable_st_term : Pulse_Syntax_Base.st_term tac_showable) =
  { show = Pulse_Syntax_Printer.st_term_to_string }
let (tac_showable_universe : Pulse_Syntax_Base.universe tac_showable) =
  {
    show =
      (fun uu___ ->
         (fun t ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> Pulse_Syntax_Printer.univ_to_string t))) uu___)
  }
let (tac_showable_comp : Pulse_Syntax_Base.comp tac_showable) =
  { show = Pulse_Syntax_Printer.comp_to_string }
let (tac_showable_env : Pulse_Typing_Env.env tac_showable) =
  { show = Pulse_Typing_Env.env_to_string }
let (tac_showable_observability :
  Pulse_Syntax_Base.observability tac_showable) =
  {
    show =
      (fun uu___ ->
         (fun o ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> Pulse_Syntax_Printer.observability_to_string o)))
           uu___)
  }
let (tac_showable_effect_annot : Pulse_Syntax_Base.effect_annot tac_showable)
  = { show = Pulse_Syntax_Printer.effect_annot_to_string }
let (tac_showable_post_hint_t : Pulse_Typing.post_hint_t tac_showable) =
  {
    show =
      (fun h ->
         let uu___ =
           let uu___1 =
             let uu___2 = show tac_showable_env h.Pulse_Typing.g in
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Show.fst"
                        (Prims.of_int (79)) (Prims.of_int (15))
                        (Prims.of_int (79)) (Prims.of_int (23)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Show.fst"
                        (Prims.of_int (79)) (Prims.of_int (15))
                        (Prims.of_int (84)) (Prims.of_int (7)))))
               (Obj.magic uu___2)
               (fun uu___3 ->
                  (fun uu___3 ->
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 =
                             show tac_showable_effect_annot
                               h.Pulse_Typing.effect_annot in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Show.fst"
                                      (Prims.of_int (80)) (Prims.of_int (26))
                                      (Prims.of_int (80)) (Prims.of_int (45)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Show.fst"
                                      (Prims.of_int (80)) (Prims.of_int (26))
                                      (Prims.of_int (84)) (Prims.of_int (7)))))
                             (Obj.magic uu___7)
                             (fun uu___8 ->
                                (fun uu___8 ->
                                   let uu___9 =
                                     let uu___10 =
                                       let uu___11 =
                                         let uu___12 =
                                           show tac_showable_term
                                             h.Pulse_Typing.ret_ty in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Show.fst"
                                                    (Prims.of_int (81))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (81))
                                                    (Prims.of_int (33)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Show.fst"
                                                    (Prims.of_int (81))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (84))
                                                    (Prims.of_int (7)))))
                                           (Obj.magic uu___12)
                                           (fun uu___13 ->
                                              (fun uu___13 ->
                                                 let uu___14 =
                                                   let uu___15 =
                                                     let uu___16 =
                                                       let uu___17 =
                                                         show
                                                           tac_showable_universe
                                                           h.Pulse_Typing.u in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Show.fst"
                                                                  (Prims.of_int (82))
                                                                  (Prims.of_int (15))
                                                                  (Prims.of_int (82))
                                                                  (Prims.of_int (23)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Show.fst"
                                                                  (Prims.of_int (82))
                                                                  (Prims.of_int (15))
                                                                  (Prims.of_int (84))
                                                                  (Prims.of_int (7)))))
                                                         (Obj.magic uu___17)
                                                         (fun uu___18 ->
                                                            (fun uu___18 ->
                                                               let uu___19 =
                                                                 let uu___20
                                                                   =
                                                                   let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    show
                                                                    tac_showable_term
                                                                    h.Pulse_Typing.post in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___23
                                                                    "; }")) in
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    Prims.strcat
                                                                    "post = "
                                                                    uu___22)) in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (7)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                   (Obj.magic
                                                                    uu___20)
                                                                   (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    Prims.strcat
                                                                    "; "
                                                                    uu___21)) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (7)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___19)
                                                                    (
                                                                    fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___18
                                                                    uu___20))))
                                                              uu___18) in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Show.fst"
                                                                (Prims.of_int (82))
                                                                (Prims.of_int (15))
                                                                (Prims.of_int (84))
                                                                (Prims.of_int (7)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "prims.fst"
                                                                (Prims.of_int (611))
                                                                (Prims.of_int (19))
                                                                (Prims.of_int (611))
                                                                (Prims.of_int (31)))))
                                                       (Obj.magic uu___16)
                                                       (fun uu___17 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___18 ->
                                                               Prims.strcat
                                                                 "u = "
                                                                 uu___17)) in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Show.fst"
                                                              (Prims.of_int (82))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (84))
                                                              (Prims.of_int (7)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "prims.fst"
                                                              (Prims.of_int (611))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (611))
                                                              (Prims.of_int (31)))))
                                                     (Obj.magic uu___15)
                                                     (fun uu___16 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___17 ->
                                                             Prims.strcat
                                                               "; " uu___16)) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Show.fst"
                                                               (Prims.of_int (81))
                                                               (Prims.of_int (36))
                                                               (Prims.of_int (84))
                                                               (Prims.of_int (7)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "prims.fst"
                                                               (Prims.of_int (611))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (611))
                                                               (Prims.of_int (31)))))
                                                      (Obj.magic uu___14)
                                                      (fun uu___15 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___16 ->
                                                              Prims.strcat
                                                                uu___13
                                                                uu___15))))
                                                uu___13) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Show.fst"
                                                  (Prims.of_int (81))
                                                  (Prims.of_int (20))
                                                  (Prims.of_int (84))
                                                  (Prims.of_int (7)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "prims.fst"
                                                  (Prims.of_int (611))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (611))
                                                  (Prims.of_int (31)))))
                                         (Obj.magic uu___11)
                                         (fun uu___12 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___13 ->
                                                 Prims.strcat "ret_ty = "
                                                   uu___12)) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Show.fst"
                                                (Prims.of_int (81))
                                                (Prims.of_int (6))
                                                (Prims.of_int (84))
                                                (Prims.of_int (7)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "prims.fst"
                                                (Prims.of_int (611))
                                                (Prims.of_int (19))
                                                (Prims.of_int (611))
                                                (Prims.of_int (31)))))
                                       (Obj.magic uu___10)
                                       (fun uu___11 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___12 ->
                                               Prims.strcat "; " uu___11)) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Show.fst"
                                                 (Prims.of_int (80))
                                                 (Prims.of_int (48))
                                                 (Prims.of_int (84))
                                                 (Prims.of_int (7)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "prims.fst"
                                                 (Prims.of_int (611))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (611))
                                                 (Prims.of_int (31)))))
                                        (Obj.magic uu___9)
                                        (fun uu___10 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___11 ->
                                                Prims.strcat uu___8 uu___10))))
                                  uu___8) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Show.fst"
                                    (Prims.of_int (80)) (Prims.of_int (26))
                                    (Prims.of_int (84)) (Prims.of_int (7)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "prims.fst"
                                    (Prims.of_int (611)) (Prims.of_int (19))
                                    (Prims.of_int (611)) (Prims.of_int (31)))))
                           (Obj.magic uu___6)
                           (fun uu___7 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___8 ->
                                   Prims.strcat "effect_annot = " uu___7)) in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Show.fst"
                                  (Prims.of_int (80)) (Prims.of_int (6))
                                  (Prims.of_int (84)) (Prims.of_int (7)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "prims.fst"
                                  (Prims.of_int (611)) (Prims.of_int (19))
                                  (Prims.of_int (611)) (Prims.of_int (31)))))
                         (Obj.magic uu___5)
                         (fun uu___6 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___7 -> Prims.strcat "; " uu___6)) in
                     Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Show.fst"
                                   (Prims.of_int (79)) (Prims.of_int (26))
                                   (Prims.of_int (84)) (Prims.of_int (7)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "prims.fst"
                                   (Prims.of_int (611)) (Prims.of_int (19))
                                   (Prims.of_int (611)) (Prims.of_int (31)))))
                          (Obj.magic uu___4)
                          (fun uu___5 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___6 -> Prims.strcat uu___3 uu___5))))
                    uu___3) in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.Show.fst" (Prims.of_int (79))
                      (Prims.of_int (15)) (Prims.of_int (84))
                      (Prims.of_int (7)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "prims.fst" (Prims.of_int (611))
                      (Prims.of_int (19)) (Prims.of_int (611))
                      (Prims.of_int (31))))) (Obj.magic uu___1)
             (fun uu___2 ->
                FStar_Tactics_Effect.lift_div_tac
                  (fun uu___3 -> Prims.strcat "g = " uu___2)) in
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.Show.fst" (Prims.of_int (79))
                    (Prims.of_int (6)) (Prims.of_int (84)) (Prims.of_int (7)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "prims.fst" (Prims.of_int (611))
                    (Prims.of_int (19)) (Prims.of_int (611))
                    (Prims.of_int (31))))) (Obj.magic uu___)
           (fun uu___1 ->
              FStar_Tactics_Effect.lift_div_tac
                (fun uu___2 -> Prims.strcat "{" uu___1)))
  }
let (tac_showable_r_term : FStar_Reflection_Types.term tac_showable) =
  { show = FStar_Tactics_V1_Builtins.term_to_string }
let (tac_showable_range : FStar_Range.range tac_showable) =
  { show = FStar_Tactics_V1_Builtins.range_to_string }
let tac_showable_tuple2 :
  'a 'b . 'a tac_showable -> 'b tac_showable -> ('a * 'b) tac_showable =
  fun uu___ ->
    fun uu___1 ->
      {
        show =
          (fun uu___2 ->
             match uu___2 with
             | (x, y) ->
                 let uu___3 =
                   let uu___4 = show uu___ x in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Show.fst"
                              (Prims.of_int (96)) (Prims.of_int (30))
                              (Prims.of_int (96)) (Prims.of_int (36)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Show.fst"
                              (Prims.of_int (96)) (Prims.of_int (30))
                              (Prims.of_int (96)) (Prims.of_int (58)))))
                     (Obj.magic uu___4)
                     (fun uu___5 ->
                        (fun uu___5 ->
                           let uu___6 =
                             let uu___7 =
                               let uu___8 = show uu___1 y in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Pulse.Show.fst"
                                          (Prims.of_int (96))
                                          (Prims.of_int (46))
                                          (Prims.of_int (96))
                                          (Prims.of_int (52)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___8)
                                 (fun uu___9 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___10 -> Prims.strcat uu___9 ")")) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.Show.fst"
                                        (Prims.of_int (96))
                                        (Prims.of_int (46))
                                        (Prims.of_int (96))
                                        (Prims.of_int (58)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___7)
                               (fun uu___8 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___9 -> Prims.strcat ", " uu___8)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Pulse.Show.fst"
                                         (Prims.of_int (96))
                                         (Prims.of_int (39))
                                         (Prims.of_int (96))
                                         (Prims.of_int (58)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___6)
                                (fun uu___7 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___8 ->
                                        Prims.strcat uu___5 uu___7)))) uu___5) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Show.fst"
                            (Prims.of_int (96)) (Prims.of_int (30))
                            (Prims.of_int (96)) (Prims.of_int (58)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___5 -> Prims.strcat "(" uu___4)))
      }
let tac_showable_tuple3 :
  'a 'b 'c .
    'a tac_showable ->
      'b tac_showable -> 'c tac_showable -> ('a * 'b * 'c) tac_showable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        {
          show =
            (fun uu___3 ->
               match uu___3 with
               | (x, y, z) ->
                   let uu___4 =
                     let uu___5 = show uu___ x in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Show.fst"
                                (Prims.of_int (100)) (Prims.of_int (33))
                                (Prims.of_int (100)) (Prims.of_int (39)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Show.fst"
                                (Prims.of_int (100)) (Prims.of_int (33))
                                (Prims.of_int (100)) (Prims.of_int (77)))))
                       (Obj.magic uu___5)
                       (fun uu___6 ->
                          (fun uu___6 ->
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 = show uu___1 y in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Show.fst"
                                            (Prims.of_int (100))
                                            (Prims.of_int (49))
                                            (Prims.of_int (100))
                                            (Prims.of_int (55)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Show.fst"
                                            (Prims.of_int (100))
                                            (Prims.of_int (49))
                                            (Prims.of_int (100))
                                            (Prims.of_int (77)))))
                                   (Obj.magic uu___9)
                                   (fun uu___10 ->
                                      (fun uu___10 ->
                                         let uu___11 =
                                           let uu___12 =
                                             let uu___13 = show uu___2 z in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Show.fst"
                                                        (Prims.of_int (100))
                                                        (Prims.of_int (65))
                                                        (Prims.of_int (100))
                                                        (Prims.of_int (71)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "prims.fst"
                                                        (Prims.of_int (611))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (611))
                                                        (Prims.of_int (31)))))
                                               (Obj.magic uu___13)
                                               (fun uu___14 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___15 ->
                                                       Prims.strcat uu___14
                                                         ")")) in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Show.fst"
                                                      (Prims.of_int (100))
                                                      (Prims.of_int (65))
                                                      (Prims.of_int (100))
                                                      (Prims.of_int (77)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "prims.fst"
                                                      (Prims.of_int (611))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (611))
                                                      (Prims.of_int (31)))))
                                             (Obj.magic uu___12)
                                             (fun uu___13 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___14 ->
                                                     Prims.strcat ", "
                                                       uu___13)) in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Show.fst"
                                                       (Prims.of_int (100))
                                                       (Prims.of_int (58))
                                                       (Prims.of_int (100))
                                                       (Prims.of_int (77)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "prims.fst"
                                                       (Prims.of_int (611))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (611))
                                                       (Prims.of_int (31)))))
                                              (Obj.magic uu___11)
                                              (fun uu___12 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___13 ->
                                                      Prims.strcat uu___10
                                                        uu___12)))) uu___10) in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Pulse.Show.fst"
                                          (Prims.of_int (100))
                                          (Prims.of_int (49))
                                          (Prims.of_int (100))
                                          (Prims.of_int (77)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___8)
                                 (fun uu___9 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___10 ->
                                         Prims.strcat ", " uu___9)) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Show.fst"
                                           (Prims.of_int (100))
                                           (Prims.of_int (42))
                                           (Prims.of_int (100))
                                           (Prims.of_int (77)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "prims.fst"
                                           (Prims.of_int (611))
                                           (Prims.of_int (19))
                                           (Prims.of_int (611))
                                           (Prims.of_int (31)))))
                                  (Obj.magic uu___7)
                                  (fun uu___8 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___9 ->
                                          Prims.strcat uu___6 uu___8))))
                            uu___6) in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Show.fst"
                              (Prims.of_int (100)) (Prims.of_int (33))
                              (Prims.of_int (100)) (Prims.of_int (77)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic uu___4)
                     (fun uu___5 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___6 -> Prims.strcat "(" uu___5)))
        }
let tac_showable_tuple4 :
  'a 'b 'c 'd .
    'a tac_showable ->
      'b tac_showable ->
        'c tac_showable ->
          'd tac_showable -> ('a * 'b * 'c * 'd) tac_showable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          {
            show =
              (fun uu___4 ->
                 match uu___4 with
                 | (x, y, z, w) ->
                     let uu___5 =
                       let uu___6 = show uu___ x in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Show.fst"
                                  (Prims.of_int (104)) (Prims.of_int (36))
                                  (Prims.of_int (104)) (Prims.of_int (42)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Show.fst"
                                  (Prims.of_int (104)) (Prims.of_int (36))
                                  (Prims.of_int (104)) (Prims.of_int (96)))))
                         (Obj.magic uu___6)
                         (fun uu___7 ->
                            (fun uu___7 ->
                               let uu___8 =
                                 let uu___9 =
                                   let uu___10 = show uu___1 y in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Show.fst"
                                              (Prims.of_int (104))
                                              (Prims.of_int (52))
                                              (Prims.of_int (104))
                                              (Prims.of_int (58)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Show.fst"
                                              (Prims.of_int (104))
                                              (Prims.of_int (52))
                                              (Prims.of_int (104))
                                              (Prims.of_int (96)))))
                                     (Obj.magic uu___10)
                                     (fun uu___11 ->
                                        (fun uu___11 ->
                                           let uu___12 =
                                             let uu___13 =
                                               let uu___14 = show uu___2 z in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Show.fst"
                                                          (Prims.of_int (104))
                                                          (Prims.of_int (68))
                                                          (Prims.of_int (104))
                                                          (Prims.of_int (74)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Show.fst"
                                                          (Prims.of_int (104))
                                                          (Prims.of_int (68))
                                                          (Prims.of_int (104))
                                                          (Prims.of_int (96)))))
                                                 (Obj.magic uu___14)
                                                 (fun uu___15 ->
                                                    (fun uu___15 ->
                                                       let uu___16 =
                                                         let uu___17 =
                                                           let uu___18 =
                                                             show uu___3 w in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (90)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                             (Obj.magic
                                                                uu___18)
                                                             (fun uu___19 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun
                                                                    uu___20
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___19
                                                                    ")")) in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (96)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                           (Obj.magic uu___17)
                                                           (fun uu___18 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___19
                                                                   ->
                                                                   Prims.strcat
                                                                    ", "
                                                                    uu___18)) in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (96)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                            (Obj.magic
                                                               uu___16)
                                                            (fun uu___17 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___18
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___15
                                                                    uu___17))))
                                                      uu___15) in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Show.fst"
                                                        (Prims.of_int (104))
                                                        (Prims.of_int (68))
                                                        (Prims.of_int (104))
                                                        (Prims.of_int (96)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "prims.fst"
                                                        (Prims.of_int (611))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (611))
                                                        (Prims.of_int (31)))))
                                               (Obj.magic uu___13)
                                               (fun uu___14 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___15 ->
                                                       Prims.strcat ", "
                                                         uu___14)) in
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Show.fst"
                                                         (Prims.of_int (104))
                                                         (Prims.of_int (61))
                                                         (Prims.of_int (104))
                                                         (Prims.of_int (96)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (611))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (611))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic uu___12)
                                                (fun uu___13 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___14 ->
                                                        Prims.strcat uu___11
                                                          uu___13)))) uu___11) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Show.fst"
                                            (Prims.of_int (104))
                                            (Prims.of_int (52))
                                            (Prims.of_int (104))
                                            (Prims.of_int (96)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "prims.fst"
                                            (Prims.of_int (611))
                                            (Prims.of_int (19))
                                            (Prims.of_int (611))
                                            (Prims.of_int (31)))))
                                   (Obj.magic uu___9)
                                   (fun uu___10 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___11 ->
                                           Prims.strcat ", " uu___10)) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Show.fst"
                                             (Prims.of_int (104))
                                             (Prims.of_int (45))
                                             (Prims.of_int (104))
                                             (Prims.of_int (96)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (611))
                                             (Prims.of_int (19))
                                             (Prims.of_int (611))
                                             (Prims.of_int (31)))))
                                    (Obj.magic uu___8)
                                    (fun uu___9 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___10 ->
                                            Prims.strcat uu___7 uu___9))))
                              uu___7) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Show.fst"
                                (Prims.of_int (104)) (Prims.of_int (36))
                                (Prims.of_int (104)) (Prims.of_int (96)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "prims.fst"
                                (Prims.of_int (611)) (Prims.of_int (19))
                                (Prims.of_int (611)) (Prims.of_int (31)))))
                       (Obj.magic uu___5)
                       (fun uu___6 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___7 -> Prims.strcat "(" uu___6)))
          }
let tac_showable_tuple5 :
  'a 'b 'c 'd 'e .
    'a tac_showable ->
      'b tac_showable ->
        'c tac_showable ->
          'd tac_showable ->
            'e tac_showable -> ('a * 'b * 'c * 'd * 'e) tac_showable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            {
              show =
                (fun uu___5 ->
                   match uu___5 with
                   | (x, y, z, w, v) ->
                       let uu___6 =
                         let uu___7 = show uu___ x in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Show.fst"
                                    (Prims.of_int (108)) (Prims.of_int (39))
                                    (Prims.of_int (108)) (Prims.of_int (45)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Show.fst"
                                    (Prims.of_int (108)) (Prims.of_int (39))
                                    (Prims.of_int (108)) (Prims.of_int (115)))))
                           (Obj.magic uu___7)
                           (fun uu___8 ->
                              (fun uu___8 ->
                                 let uu___9 =
                                   let uu___10 =
                                     let uu___11 = show uu___1 y in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Show.fst"
                                                (Prims.of_int (108))
                                                (Prims.of_int (55))
                                                (Prims.of_int (108))
                                                (Prims.of_int (61)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Show.fst"
                                                (Prims.of_int (108))
                                                (Prims.of_int (55))
                                                (Prims.of_int (108))
                                                (Prims.of_int (115)))))
                                       (Obj.magic uu___11)
                                       (fun uu___12 ->
                                          (fun uu___12 ->
                                             let uu___13 =
                                               let uu___14 =
                                                 let uu___15 = show uu___2 z in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Show.fst"
                                                            (Prims.of_int (108))
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (108))
                                                            (Prims.of_int (77)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Show.fst"
                                                            (Prims.of_int (108))
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (108))
                                                            (Prims.of_int (115)))))
                                                   (Obj.magic uu___15)
                                                   (fun uu___16 ->
                                                      (fun uu___16 ->
                                                         let uu___17 =
                                                           let uu___18 =
                                                             let uu___19 =
                                                               show uu___3 w in
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (93)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (115)))))
                                                               (Obj.magic
                                                                  uu___19)
                                                               (fun uu___20
                                                                  ->
                                                                  (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    show
                                                                    uu___4 v in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (109)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___24
                                                                    ")")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    Prims.strcat
                                                                    ", "
                                                                    uu___23)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___20
                                                                    uu___22))))
                                                                    uu___20) in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (115)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                             (Obj.magic
                                                                uu___18)
                                                             (fun uu___19 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun
                                                                    uu___20
                                                                    ->
                                                                    Prims.strcat
                                                                    ", "
                                                                    uu___19)) in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (115)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                              (Obj.magic
                                                                 uu___17)
                                                              (fun uu___18 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___19
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___16
                                                                    uu___18))))
                                                        uu___16) in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Show.fst"
                                                          (Prims.of_int (108))
                                                          (Prims.of_int (71))
                                                          (Prims.of_int (108))
                                                          (Prims.of_int (115)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "prims.fst"
                                                          (Prims.of_int (611))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (611))
                                                          (Prims.of_int (31)))))
                                                 (Obj.magic uu___14)
                                                 (fun uu___15 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___16 ->
                                                         Prims.strcat ", "
                                                           uu___15)) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Show.fst"
                                                           (Prims.of_int (108))
                                                           (Prims.of_int (64))
                                                           (Prims.of_int (108))
                                                           (Prims.of_int (115)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "prims.fst"
                                                           (Prims.of_int (611))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (611))
                                                           (Prims.of_int (31)))))
                                                  (Obj.magic uu___13)
                                                  (fun uu___14 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___15 ->
                                                          Prims.strcat
                                                            uu___12 uu___14))))
                                            uu___12) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Show.fst"
                                              (Prims.of_int (108))
                                              (Prims.of_int (55))
                                              (Prims.of_int (108))
                                              (Prims.of_int (115)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range "prims.fst"
                                              (Prims.of_int (611))
                                              (Prims.of_int (19))
                                              (Prims.of_int (611))
                                              (Prims.of_int (31)))))
                                     (Obj.magic uu___10)
                                     (fun uu___11 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___12 ->
                                             Prims.strcat ", " uu___11)) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Show.fst"
                                               (Prims.of_int (108))
                                               (Prims.of_int (48))
                                               (Prims.of_int (108))
                                               (Prims.of_int (115)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "prims.fst"
                                               (Prims.of_int (611))
                                               (Prims.of_int (19))
                                               (Prims.of_int (611))
                                               (Prims.of_int (31)))))
                                      (Obj.magic uu___9)
                                      (fun uu___10 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___11 ->
                                              Prims.strcat uu___8 uu___10))))
                                uu___8) in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Show.fst"
                                  (Prims.of_int (108)) (Prims.of_int (39))
                                  (Prims.of_int (108)) (Prims.of_int (115)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "prims.fst"
                                  (Prims.of_int (611)) (Prims.of_int (19))
                                  (Prims.of_int (611)) (Prims.of_int (31)))))
                         (Obj.magic uu___6)
                         (fun uu___7 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___8 -> Prims.strcat "(" uu___7)))
            }
let tac_showable_tuple6 :
  'a 'b 'c 'd 'e 'f .
    'a tac_showable ->
      'b tac_showable ->
        'c tac_showable ->
          'd tac_showable ->
            'e tac_showable ->
              'f tac_showable -> ('a * 'b * 'c * 'd * 'e * 'f) tac_showable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            fun uu___5 ->
              {
                show =
                  (fun uu___6 ->
                     match uu___6 with
                     | (x, y, z, w, v, u) ->
                         let uu___7 =
                           let uu___8 = show uu___ x in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Show.fst"
                                      (Prims.of_int (112))
                                      (Prims.of_int (42))
                                      (Prims.of_int (112))
                                      (Prims.of_int (48)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Show.fst"
                                      (Prims.of_int (112))
                                      (Prims.of_int (42))
                                      (Prims.of_int (112))
                                      (Prims.of_int (134)))))
                             (Obj.magic uu___8)
                             (fun uu___9 ->
                                (fun uu___9 ->
                                   let uu___10 =
                                     let uu___11 =
                                       let uu___12 = show uu___1 y in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Show.fst"
                                                  (Prims.of_int (112))
                                                  (Prims.of_int (58))
                                                  (Prims.of_int (112))
                                                  (Prims.of_int (64)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Show.fst"
                                                  (Prims.of_int (112))
                                                  (Prims.of_int (58))
                                                  (Prims.of_int (112))
                                                  (Prims.of_int (134)))))
                                         (Obj.magic uu___12)
                                         (fun uu___13 ->
                                            (fun uu___13 ->
                                               let uu___14 =
                                                 let uu___15 =
                                                   let uu___16 =
                                                     show uu___2 z in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Show.fst"
                                                              (Prims.of_int (112))
                                                              (Prims.of_int (74))
                                                              (Prims.of_int (112))
                                                              (Prims.of_int (80)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Show.fst"
                                                              (Prims.of_int (112))
                                                              (Prims.of_int (74))
                                                              (Prims.of_int (112))
                                                              (Prims.of_int (134)))))
                                                     (Obj.magic uu___16)
                                                     (fun uu___17 ->
                                                        (fun uu___17 ->
                                                           let uu___18 =
                                                             let uu___19 =
                                                               let uu___20 =
                                                                 show uu___3
                                                                   w in
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (96)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (134)))))
                                                                 (Obj.magic
                                                                    uu___20)
                                                                 (fun uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    show
                                                                    uu___4 v in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (112)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (134)))))
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
                                                                    let uu___28
                                                                    =
                                                                    show
                                                                    uu___5 u in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (128)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___29
                                                                    ")")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (134)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    Prims.strcat
                                                                    ", "
                                                                    uu___28)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (134)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___25
                                                                    uu___27))))
                                                                    uu___25) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (134)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    Prims.strcat
                                                                    ", "
                                                                    uu___24)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (134)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___21
                                                                    uu___23))))
                                                                    uu___21) in
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (134)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                               (Obj.magic
                                                                  uu___19)
                                                               (fun uu___20
                                                                  ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___21
                                                                    ->
                                                                    Prims.strcat
                                                                    ", "
                                                                    uu___20)) in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (134)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                (Obj.magic
                                                                   uu___18)
                                                                (fun uu___19
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___17
                                                                    uu___19))))
                                                          uu___17) in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Show.fst"
                                                            (Prims.of_int (112))
                                                            (Prims.of_int (74))
                                                            (Prims.of_int (112))
                                                            (Prims.of_int (134)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "prims.fst"
                                                            (Prims.of_int (611))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (611))
                                                            (Prims.of_int (31)))))
                                                   (Obj.magic uu___15)
                                                   (fun uu___16 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___17 ->
                                                           Prims.strcat ", "
                                                             uu___16)) in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Show.fst"
                                                             (Prims.of_int (112))
                                                             (Prims.of_int (67))
                                                             (Prims.of_int (112))
                                                             (Prims.of_int (134)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "prims.fst"
                                                             (Prims.of_int (611))
                                                             (Prims.of_int (19))
                                                             (Prims.of_int (611))
                                                             (Prims.of_int (31)))))
                                                    (Obj.magic uu___14)
                                                    (fun uu___15 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___16 ->
                                                            Prims.strcat
                                                              uu___13 uu___15))))
                                              uu___13) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Show.fst"
                                                (Prims.of_int (112))
                                                (Prims.of_int (58))
                                                (Prims.of_int (112))
                                                (Prims.of_int (134)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "prims.fst"
                                                (Prims.of_int (611))
                                                (Prims.of_int (19))
                                                (Prims.of_int (611))
                                                (Prims.of_int (31)))))
                                       (Obj.magic uu___11)
                                       (fun uu___12 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___13 ->
                                               Prims.strcat ", " uu___12)) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Show.fst"
                                                 (Prims.of_int (112))
                                                 (Prims.of_int (51))
                                                 (Prims.of_int (112))
                                                 (Prims.of_int (134)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "prims.fst"
                                                 (Prims.of_int (611))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (611))
                                                 (Prims.of_int (31)))))
                                        (Obj.magic uu___10)
                                        (fun uu___11 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___12 ->
                                                Prims.strcat uu___9 uu___11))))
                                  uu___9) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Show.fst"
                                    (Prims.of_int (112)) (Prims.of_int (42))
                                    (Prims.of_int (112)) (Prims.of_int (134)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "prims.fst"
                                    (Prims.of_int (611)) (Prims.of_int (19))
                                    (Prims.of_int (611)) (Prims.of_int (31)))))
                           (Obj.magic uu___7)
                           (fun uu___8 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___9 -> Prims.strcat "(" uu___8)))
              }
let tac_showable_tuple7 :
  'a 'b 'c 'd 'e 'f 'g .
    'a tac_showable ->
      'b tac_showable ->
        'c tac_showable ->
          'd tac_showable ->
            'e tac_showable ->
              'f tac_showable ->
                'g tac_showable ->
                  ('a * 'b * 'c * 'd * 'e * 'f * 'g) tac_showable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            fun uu___5 ->
              fun uu___6 ->
                {
                  show =
                    (fun uu___7 ->
                       match uu___7 with
                       | (x, y, z, w, v, u, t) ->
                           let uu___8 =
                             let uu___9 = show uu___ x in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.Show.fst"
                                        (Prims.of_int (116))
                                        (Prims.of_int (45))
                                        (Prims.of_int (116))
                                        (Prims.of_int (51)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.Show.fst"
                                        (Prims.of_int (116))
                                        (Prims.of_int (45))
                                        (Prims.of_int (116))
                                        (Prims.of_int (153)))))
                               (Obj.magic uu___9)
                               (fun uu___10 ->
                                  (fun uu___10 ->
                                     let uu___11 =
                                       let uu___12 =
                                         let uu___13 = show uu___1 y in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Show.fst"
                                                    (Prims.of_int (116))
                                                    (Prims.of_int (61))
                                                    (Prims.of_int (116))
                                                    (Prims.of_int (67)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Show.fst"
                                                    (Prims.of_int (116))
                                                    (Prims.of_int (61))
                                                    (Prims.of_int (116))
                                                    (Prims.of_int (153)))))
                                           (Obj.magic uu___13)
                                           (fun uu___14 ->
                                              (fun uu___14 ->
                                                 let uu___15 =
                                                   let uu___16 =
                                                     let uu___17 =
                                                       show uu___2 z in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Show.fst"
                                                                (Prims.of_int (116))
                                                                (Prims.of_int (77))
                                                                (Prims.of_int (116))
                                                                (Prims.of_int (83)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Show.fst"
                                                                (Prims.of_int (116))
                                                                (Prims.of_int (77))
                                                                (Prims.of_int (116))
                                                                (Prims.of_int (153)))))
                                                       (Obj.magic uu___17)
                                                       (fun uu___18 ->
                                                          (fun uu___18 ->
                                                             let uu___19 =
                                                               let uu___20 =
                                                                 let uu___21
                                                                   =
                                                                   show
                                                                    uu___3 w in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (99)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (153)))))
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
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    show
                                                                    uu___4 v in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (153)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    show
                                                                    uu___5 u in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (131)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (153)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    show
                                                                    uu___6 t in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (147)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___34
                                                                    ")")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (153)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    Prims.strcat
                                                                    ", "
                                                                    uu___33)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (153)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___31)
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___30
                                                                    uu___32))))
                                                                    uu___30) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (153)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    Prims.strcat
                                                                    ", "
                                                                    uu___29)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (153)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___26
                                                                    uu___28))))
                                                                    uu___26) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (153)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    Prims.strcat
                                                                    ", "
                                                                    uu___25)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (153)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___22
                                                                    uu___24))))
                                                                    uu___22) in
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (153)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                 (Obj.magic
                                                                    uu___20)
                                                                 (fun uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    Prims.strcat
                                                                    ", "
                                                                    uu___21)) in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Show.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (153)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
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
                                                                    Prims.strcat
                                                                    uu___18
                                                                    uu___20))))
                                                            uu___18) in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Show.fst"
                                                              (Prims.of_int (116))
                                                              (Prims.of_int (77))
                                                              (Prims.of_int (116))
                                                              (Prims.of_int (153)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "prims.fst"
                                                              (Prims.of_int (611))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (611))
                                                              (Prims.of_int (31)))))
                                                     (Obj.magic uu___16)
                                                     (fun uu___17 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___18 ->
                                                             Prims.strcat
                                                               ", " uu___17)) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Show.fst"
                                                               (Prims.of_int (116))
                                                               (Prims.of_int (70))
                                                               (Prims.of_int (116))
                                                               (Prims.of_int (153)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "prims.fst"
                                                               (Prims.of_int (611))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (611))
                                                               (Prims.of_int (31)))))
                                                      (Obj.magic uu___15)
                                                      (fun uu___16 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___17 ->
                                                              Prims.strcat
                                                                uu___14
                                                                uu___16))))
                                                uu___14) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Show.fst"
                                                  (Prims.of_int (116))
                                                  (Prims.of_int (61))
                                                  (Prims.of_int (116))
                                                  (Prims.of_int (153)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "prims.fst"
                                                  (Prims.of_int (611))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (611))
                                                  (Prims.of_int (31)))))
                                         (Obj.magic uu___12)
                                         (fun uu___13 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___14 ->
                                                 Prims.strcat ", " uu___13)) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Show.fst"
                                                   (Prims.of_int (116))
                                                   (Prims.of_int (54))
                                                   (Prims.of_int (116))
                                                   (Prims.of_int (153)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (611))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (611))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic uu___11)
                                          (fun uu___12 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___13 ->
                                                  Prims.strcat uu___10
                                                    uu___12)))) uu___10) in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.Show.fst"
                                      (Prims.of_int (116))
                                      (Prims.of_int (45))
                                      (Prims.of_int (116))
                                      (Prims.of_int (153)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "prims.fst"
                                      (Prims.of_int (611))
                                      (Prims.of_int (19))
                                      (Prims.of_int (611))
                                      (Prims.of_int (31)))))
                             (Obj.magic uu___8)
                             (fun uu___9 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___10 -> Prims.strcat "(" uu___9)))
                }