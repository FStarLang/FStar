open Prims
let (text : Prims.string -> FStar_Pprint.document) =
  fun s ->
    FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one)
      (FStar_Pprint.words s)
let (indent : FStar_Pprint.document -> FStar_Pprint.document) =
  fun d ->
    FStar_Pprint.nest (Prims.of_int (2))
      (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline (FStar_Pprint.align d))
type 'a printable =
  {
  pp: 'a -> (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr }
let __proj__Mkprintable__item__pp :
  'a .
    'a printable ->
      'a -> (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr
  = fun projectee -> match projectee with | { pp;_} -> pp
let pp :
  'a .
    'a printable ->
      'a -> (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr
  = fun projectee -> match projectee with | { pp = pp1;_} -> pp1
let from_show : 'a . 'a Pulse_Show.tac_showable -> 'a printable =
  fun d ->
    {
      pp =
        (fun x ->
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (38))
                      (Prims.of_int (34)) (Prims.of_int (38))
                      (Prims.of_int (42)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (38))
                      (Prims.of_int (17)) (Prims.of_int (38))
                      (Prims.of_int (42)))))
             (Obj.magic (Pulse_Show.show d x))
             (fun uu___ ->
                FStar_Tactics_Effect.lift_div_tac
                  (fun uu___1 -> FStar_Pprint.arbitrary_string uu___)))
    }
let (uu___19 : Prims.string printable) = from_show Pulse_Show.uu___12
let (uu___20 : unit printable) = from_show Pulse_Show.uu___14
let (uu___21 : Prims.bool printable) = from_show Pulse_Show.uu___16
let (uu___22 : Prims.int printable) = from_show Pulse_Show.uu___18
let (uu___23 : Pulse_Syntax_Base.ctag printable) =
  from_show Pulse_Show.uu___28
let showable_option :
  'a . 'a printable -> 'a FStar_Pervasives_Native.option printable =
  fun uu___ ->
    {
      pp =
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> FStar_Pprint.doc_of_string "None")))
              | FStar_Pervasives_Native.Some v ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.PP.fst"
                                   (Prims.of_int (50)) (Prims.of_int (54))
                                   (Prims.of_int (50)) (Prims.of_int (58)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.PP.fst"
                                   (Prims.of_int (50)) (Prims.of_int (29))
                                   (Prims.of_int (50)) (Prims.of_int (58)))))
                          (Obj.magic (pp uu___ v))
                          (fun uu___2 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 ->
                                  FStar_Pprint.op_Hat_Slash_Hat
                                    (FStar_Pprint.doc_of_string "Some")
                                    uu___2))))) uu___1)
    }
let rec separate_map :
  'a .
    FStar_Pprint.document ->
      ('a -> (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr) ->
        'a Prims.list ->
          (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun sep ->
           fun f ->
             fun l ->
               match l with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> FStar_Pprint.empty)))
               | x::[] -> Obj.magic (Obj.repr (f x))
               | x::xs ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.PP.fst"
                                    (Prims.of_int (59)) (Prims.of_int (13))
                                    (Prims.of_int (59)) (Prims.of_int (16)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.PP.fst"
                                    (Prims.of_int (59)) (Prims.of_int (13))
                                    (Prims.of_int (59)) (Prims.of_int (49)))))
                           (Obj.magic (f x))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.PP.fst"
                                               (Prims.of_int (59))
                                               (Prims.of_int (20))
                                               (Prims.of_int (59))
                                               (Prims.of_int (49)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.PP.fst"
                                               (Prims.of_int (59))
                                               (Prims.of_int (13))
                                               (Prims.of_int (59))
                                               (Prims.of_int (49)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.PP.fst"
                                                     (Prims.of_int (59))
                                                     (Prims.of_int (28))
                                                     (Prims.of_int (59))
                                                     (Prims.of_int (49)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.PP.fst"
                                                     (Prims.of_int (59))
                                                     (Prims.of_int (20))
                                                     (Prims.of_int (59))
                                                     (Prims.of_int (49)))))
                                            (Obj.magic
                                               (separate_map sep f xs))
                                            (fun uu___1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                      sep uu___1))))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              FStar_Pprint.op_Hat_Hat uu___
                                                uu___1)))) uu___)))) uu___2
          uu___1 uu___
let showable_list : 'a . 'a printable -> 'a Prims.list printable =
  fun uu___ ->
    {
      pp =
        (fun l ->
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (62))
                      (Prims.of_int (26)) (Prims.of_int (62))
                      (Prims.of_int (51)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (62))
                      (Prims.of_int (17)) (Prims.of_int (62))
                      (Prims.of_int (51)))))
             (Obj.magic (separate_map FStar_Pprint.comma (pp uu___) l))
             (fun uu___1 ->
                FStar_Tactics_Effect.lift_div_tac
                  (fun uu___2 -> FStar_Pprint.brackets uu___1)))
    }
let (uu___44 : Pulse_Syntax_Base.term printable) =
  from_show Pulse_Show.uu___30
let (uu___45 : Pulse_Syntax_Base.universe printable) =
  from_show Pulse_Show.uu___31
let (uu___46 : Pulse_Syntax_Base.comp printable) =
  from_show Pulse_Show.uu___33
let (uu___47 : Pulse_Typing_Env.env printable) =
  { pp = Pulse_Typing_Env.env_to_doc }
let (pp_record :
  (Prims.string * FStar_Pprint.document) Prims.list ->
    (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun flds ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (74))
               (Prims.of_int (9)) (Prims.of_int (75)) (Prims.of_int (91)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (74))
               (Prims.of_int (2)) (Prims.of_int (75)) (Prims.of_int (91)))))
      (Obj.magic
         (separate_map (FStar_Pprint.doc_of_string ";")
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          match uu___ with
                          | (s, d) ->
                              FStar_Pprint.op_Hat_Slash_Hat
                                (FStar_Pprint.doc_of_string s)
                                (FStar_Pprint.op_Hat_Slash_Hat
                                   FStar_Pprint.equals d)))) uu___) flds))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_Pprint.braces uu___))
let (uu___52 : Pulse_Typing.post_hint_t printable) =
  {
    pp =
      (fun h ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (79))
                    (Prims.of_int (20)) (Prims.of_int (83))
                    (Prims.of_int (41)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (79))
                    (Prims.of_int (10)) (Prims.of_int (83))
                    (Prims.of_int (41)))))
           (Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.PP.fst"
                          (Prims.of_int (79)) (Prims.of_int (22))
                          (Prims.of_int (79)) (Prims.of_int (33)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.PP.fst"
                          (Prims.of_int (79)) (Prims.of_int (20))
                          (Prims.of_int (83)) (Prims.of_int (41)))))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.PP.fst"
                                (Prims.of_int (79)) (Prims.of_int (27))
                                (Prims.of_int (79)) (Prims.of_int (33)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.PP.fst"
                                (Prims.of_int (79)) (Prims.of_int (22))
                                (Prims.of_int (79)) (Prims.of_int (33)))))
                       (Obj.magic (pp uu___47 h.Pulse_Typing.g))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> ("g", uu___)))))
                 (fun uu___ ->
                    (fun uu___ ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.PP.fst"
                                     (Prims.of_int (79)) (Prims.of_int (20))
                                     (Prims.of_int (83)) (Prims.of_int (41)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.PP.fst"
                                     (Prims.of_int (79)) (Prims.of_int (20))
                                     (Prims.of_int (83)) (Prims.of_int (41)))))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "Pulse.PP.fst"
                                           (Prims.of_int (80))
                                           (Prims.of_int (22))
                                           (Prims.of_int (80))
                                           (Prims.of_int (49)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "Pulse.PP.fst"
                                           (Prims.of_int (79))
                                           (Prims.of_int (20))
                                           (Prims.of_int (83))
                                           (Prims.of_int (41)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.PP.fst"
                                                 (Prims.of_int (80))
                                                 (Prims.of_int (35))
                                                 (Prims.of_int (80))
                                                 (Prims.of_int (49)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.PP.fst"
                                                 (Prims.of_int (80))
                                                 (Prims.of_int (22))
                                                 (Prims.of_int (80))
                                                 (Prims.of_int (49)))))
                                        (Obj.magic
                                           (pp (showable_option uu___23)
                                              h.Pulse_Typing.ctag_hint))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                ("ctag_hint", uu___1)))))
                                  (fun uu___1 ->
                                     (fun uu___1 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.PP.fst"
                                                      (Prims.of_int (79))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (83))
                                                      (Prims.of_int (41)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.PP.fst"
                                                      (Prims.of_int (79))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (83))
                                                      (Prims.of_int (41)))))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.PP.fst"
                                                            (Prims.of_int (81))
                                                            (Prims.of_int (22))
                                                            (Prims.of_int (81))
                                                            (Prims.of_int (43)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.PP.fst"
                                                            (Prims.of_int (79))
                                                            (Prims.of_int (20))
                                                            (Prims.of_int (83))
                                                            (Prims.of_int (41)))))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.PP.fst"
                                                                  (Prims.of_int (81))
                                                                  (Prims.of_int (32))
                                                                  (Prims.of_int (81))
                                                                  (Prims.of_int (43)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.PP.fst"
                                                                  (Prims.of_int (81))
                                                                  (Prims.of_int (22))
                                                                  (Prims.of_int (81))
                                                                  (Prims.of_int (43)))))
                                                         (Obj.magic
                                                            (pp uu___44
                                                               h.Pulse_Typing.ret_ty))
                                                         (fun uu___2 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___3 ->
                                                                 ("ret_ty",
                                                                   uu___2)))))
                                                   (fun uu___2 ->
                                                      (fun uu___2 ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (41)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (41)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (33)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (41)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___45
                                                                    h.Pulse_Typing.u))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ("u",
                                                                    uu___3)))))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___44
                                                                    h.Pulse_Typing.post))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ("post",
                                                                    uu___4)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    [uu___4]))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___3 ::
                                                                    uu___4))))
                                                                    uu___3)))
                                                              (fun uu___3 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___4 ->
                                                                    uu___2 ::
                                                                    uu___3))))
                                                        uu___2)))
                                             (fun uu___2 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___3 -> uu___1 ::
                                                     uu___2)))) uu___1)))
                            (fun uu___1 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 -> uu___ :: uu___1)))) uu___)))
           (fun uu___ -> (fun uu___ -> Obj.magic (pp_record uu___)) uu___))
  }