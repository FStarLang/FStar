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
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (48))
                      (Prims.of_int (34)) (Prims.of_int (48))
                      (Prims.of_int (42)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (48))
                      (Prims.of_int (17)) (Prims.of_int (48))
                      (Prims.of_int (42)))))
             (Obj.magic (Pulse_Show.show d x))
             (fun uu___ ->
                FStar_Tactics_Effect.lift_div_tac
                  (fun uu___1 -> FStar_Pprint.arbitrary_string uu___)))
    }
let (printable_string : Prims.string printable) =
  from_show Pulse_Show.uu___12
let (printable_unit : unit printable) = from_show Pulse_Show.uu___14
let (printable_bool : Prims.bool printable) = from_show Pulse_Show.uu___16
let (printable_int : Prims.int printable) = from_show Pulse_Show.uu___18
let (printable_ctag : Pulse_Syntax_Base.ctag printable) =
  from_show Pulse_Show.uu___28
let printable_option :
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
                                   (Prims.of_int (60)) (Prims.of_int (54))
                                   (Prims.of_int (60)) (Prims.of_int (58)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.PP.fst"
                                   (Prims.of_int (60)) (Prims.of_int (29))
                                   (Prims.of_int (60)) (Prims.of_int (58)))))
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
                                    (Prims.of_int (69)) (Prims.of_int (13))
                                    (Prims.of_int (69)) (Prims.of_int (16)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.PP.fst"
                                    (Prims.of_int (69)) (Prims.of_int (13))
                                    (Prims.of_int (69)) (Prims.of_int (49)))))
                           (Obj.magic (f x))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.PP.fst"
                                               (Prims.of_int (69))
                                               (Prims.of_int (20))
                                               (Prims.of_int (69))
                                               (Prims.of_int (49)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.PP.fst"
                                               (Prims.of_int (69))
                                               (Prims.of_int (13))
                                               (Prims.of_int (69))
                                               (Prims.of_int (49)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.PP.fst"
                                                     (Prims.of_int (69))
                                                     (Prims.of_int (28))
                                                     (Prims.of_int (69))
                                                     (Prims.of_int (49)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.PP.fst"
                                                     (Prims.of_int (69))
                                                     (Prims.of_int (20))
                                                     (Prims.of_int (69))
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
let printable_list : 'a . 'a printable -> 'a Prims.list printable =
  fun uu___ ->
    {
      pp =
        (fun l ->
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (72))
                      (Prims.of_int (26)) (Prims.of_int (72))
                      (Prims.of_int (51)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (72))
                      (Prims.of_int (17)) (Prims.of_int (72))
                      (Prims.of_int (51)))))
             (Obj.magic (separate_map FStar_Pprint.comma (pp uu___) l))
             (fun uu___1 ->
                FStar_Tactics_Effect.lift_div_tac
                  (fun uu___2 -> FStar_Pprint.brackets uu___1)))
    }
let (printable_term : Pulse_Syntax_Base.term printable) =
  from_show Pulse_Show.uu___30
let (printable_universe : Pulse_Syntax_Base.universe printable) =
  from_show Pulse_Show.uu___31
let (printable_comp : Pulse_Syntax_Base.comp printable) =
  from_show Pulse_Show.uu___33
let (printable_env : Pulse_Typing_Env.env printable) =
  { pp = Pulse_Typing_Env.env_to_doc }
let (pp_effect_annot : Pulse_Syntax_Base.effect_annot printable) =
  from_show Pulse_Show.uu___37
let (pp_record :
  (Prims.string * FStar_Pprint.document) Prims.list ->
    (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun flds ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (87))
               (Prims.of_int (4)) (Prims.of_int (87)) (Prims.of_int (104)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (89))
               (Prims.of_int (2)) (Prims.of_int (89)) (Prims.of_int (25)))))
      (Obj.magic
         (separate_map (FStar_Pprint.doc_of_string ";")
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          match uu___ with
                          | (s, d) ->
                              FStar_Pprint.group
                                (FStar_Pprint.op_Hat_Slash_Hat
                                   (FStar_Pprint.doc_of_string s)
                                   (FStar_Pprint.op_Hat_Slash_Hat
                                      FStar_Pprint.equals
                                      (FStar_Pprint.group d)))))) uu___) flds))
      (fun flds_doc ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> FStar_Pprint.braces (FStar_Pprint.align flds_doc)))
let (printable_post_hint_t : Pulse_Typing.post_hint_t printable) =
  {
    pp =
      (fun h ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (93))
                    (Prims.of_int (20)) (Prims.of_int (97))
                    (Prims.of_int (41)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (93))
                    (Prims.of_int (10)) (Prims.of_int (97))
                    (Prims.of_int (41)))))
           (Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.PP.fst"
                          (Prims.of_int (93)) (Prims.of_int (22))
                          (Prims.of_int (93)) (Prims.of_int (33)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.PP.fst"
                          (Prims.of_int (93)) (Prims.of_int (20))
                          (Prims.of_int (97)) (Prims.of_int (41)))))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.PP.fst"
                                (Prims.of_int (93)) (Prims.of_int (27))
                                (Prims.of_int (93)) (Prims.of_int (33)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.PP.fst"
                                (Prims.of_int (93)) (Prims.of_int (22))
                                (Prims.of_int (93)) (Prims.of_int (33)))))
                       (Obj.magic (pp printable_env h.Pulse_Typing.g))
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
                                     (Prims.of_int (93)) (Prims.of_int (20))
                                     (Prims.of_int (97)) (Prims.of_int (41)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.PP.fst"
                                     (Prims.of_int (93)) (Prims.of_int (20))
                                     (Prims.of_int (97)) (Prims.of_int (41)))))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "Pulse.PP.fst"
                                           (Prims.of_int (94))
                                           (Prims.of_int (22))
                                           (Prims.of_int (94))
                                           (Prims.of_int (55)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "Pulse.PP.fst"
                                           (Prims.of_int (93))
                                           (Prims.of_int (20))
                                           (Prims.of_int (97))
                                           (Prims.of_int (41)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.PP.fst"
                                                 (Prims.of_int (94))
                                                 (Prims.of_int (38))
                                                 (Prims.of_int (94))
                                                 (Prims.of_int (55)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.PP.fst"
                                                 (Prims.of_int (94))
                                                 (Prims.of_int (22))
                                                 (Prims.of_int (94))
                                                 (Prims.of_int (55)))))
                                        (Obj.magic
                                           (pp pp_effect_annot
                                              h.Pulse_Typing.effect_annot))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                ("effect_annot", uu___1)))))
                                  (fun uu___1 ->
                                     (fun uu___1 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.PP.fst"
                                                      (Prims.of_int (93))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (97))
                                                      (Prims.of_int (41)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.PP.fst"
                                                      (Prims.of_int (93))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (97))
                                                      (Prims.of_int (41)))))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.PP.fst"
                                                            (Prims.of_int (95))
                                                            (Prims.of_int (22))
                                                            (Prims.of_int (95))
                                                            (Prims.of_int (43)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.PP.fst"
                                                            (Prims.of_int (93))
                                                            (Prims.of_int (20))
                                                            (Prims.of_int (97))
                                                            (Prims.of_int (41)))))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.PP.fst"
                                                                  (Prims.of_int (95))
                                                                  (Prims.of_int (32))
                                                                  (Prims.of_int (95))
                                                                  (Prims.of_int (43)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.PP.fst"
                                                                  (Prims.of_int (95))
                                                                  (Prims.of_int (22))
                                                                  (Prims.of_int (95))
                                                                  (Prims.of_int (43)))))
                                                         (Obj.magic
                                                            (pp
                                                               printable_term
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
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (41)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (41)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (33)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (41)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    printable_universe
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
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    printable_term
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
let (printable_fstar_term : FStar_Reflection_Types.term printable) =
  {
    pp =
      (fun t ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (102))
                    (Prims.of_int (31)) (Prims.of_int (102))
                    (Prims.of_int (60)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (102))
                    (Prims.of_int (17)) (Prims.of_int (102))
                    (Prims.of_int (60)))))
           (Obj.magic (FStar_Tactics_V2_Builtins.term_to_string t))
           (fun uu___ ->
              FStar_Tactics_Effect.lift_div_tac
                (fun uu___1 -> FStar_Pprint.doc_of_string uu___)))
  }
let printable_tuple2 :
  'a 'b . 'a printable -> 'b printable -> ('a * 'b) printable =
  fun uu___ ->
    fun uu___1 ->
      {
        pp =
          (fun uu___2 ->
             match uu___2 with
             | (x, y) ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.PP.fst"
                            (Prims.of_int (107)) (Prims.of_int (31))
                            (Prims.of_int (107)) (Prims.of_int (60)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.PP.fst"
                            (Prims.of_int (107)) (Prims.of_int (24))
                            (Prims.of_int (107)) (Prims.of_int (60)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.PP.fst"
                                  (Prims.of_int (107)) (Prims.of_int (47))
                                  (Prims.of_int (107)) (Prims.of_int (59)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.PP.fst"
                                  (Prims.of_int (107)) (Prims.of_int (31))
                                  (Prims.of_int (107)) (Prims.of_int (60)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.PP.fst"
                                        (Prims.of_int (107))
                                        (Prims.of_int (48))
                                        (Prims.of_int (107))
                                        (Prims.of_int (52)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.PP.fst"
                                        (Prims.of_int (107))
                                        (Prims.of_int (47))
                                        (Prims.of_int (107))
                                        (Prims.of_int (59)))))
                               (Obj.magic (pp uu___ x))
                               (fun uu___3 ->
                                  (fun uu___3 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.PP.fst"
                                                   (Prims.of_int (107))
                                                   (Prims.of_int (47))
                                                   (Prims.of_int (107))
                                                   (Prims.of_int (59)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.PP.fst"
                                                   (Prims.of_int (107))
                                                   (Prims.of_int (47))
                                                   (Prims.of_int (107))
                                                   (Prims.of_int (59)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.PP.fst"
                                                         (Prims.of_int (107))
                                                         (Prims.of_int (54))
                                                         (Prims.of_int (107))
                                                         (Prims.of_int (58)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.PP.fst"
                                                         (Prims.of_int (107))
                                                         (Prims.of_int (47))
                                                         (Prims.of_int (107))
                                                         (Prims.of_int (59)))))
                                                (Obj.magic (pp uu___1 y))
                                                (fun uu___4 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___5 -> [uu___4]))))
                                          (fun uu___4 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___5 -> uu___3 ::
                                                  uu___4)))) uu___3)))
                         (fun uu___3 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___4 ->
                                 FStar_Pprint.separate FStar_Pprint.comma
                                   uu___3))))
                   (fun uu___3 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___4 -> FStar_Pprint.parens uu___3)))
      }
let printable_tuple3 :
  'a 'b 'c .
    'a printable -> 'b printable -> 'c printable -> ('a * 'b * 'c) printable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        {
          pp =
            (fun uu___3 ->
               match uu___3 with
               | (x, y, z) ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.PP.fst"
                              (Prims.of_int (112)) (Prims.of_int (34))
                              (Prims.of_int (112)) (Prims.of_int (69)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.PP.fst"
                              (Prims.of_int (112)) (Prims.of_int (27))
                              (Prims.of_int (112)) (Prims.of_int (69)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.PP.fst"
                                    (Prims.of_int (112)) (Prims.of_int (50))
                                    (Prims.of_int (112)) (Prims.of_int (68)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.PP.fst"
                                    (Prims.of_int (112)) (Prims.of_int (34))
                                    (Prims.of_int (112)) (Prims.of_int (69)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Pulse.PP.fst"
                                          (Prims.of_int (112))
                                          (Prims.of_int (51))
                                          (Prims.of_int (112))
                                          (Prims.of_int (55)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Pulse.PP.fst"
                                          (Prims.of_int (112))
                                          (Prims.of_int (50))
                                          (Prims.of_int (112))
                                          (Prims.of_int (68)))))
                                 (Obj.magic (pp uu___ x))
                                 (fun uu___4 ->
                                    (fun uu___4 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.PP.fst"
                                                     (Prims.of_int (112))
                                                     (Prims.of_int (50))
                                                     (Prims.of_int (112))
                                                     (Prims.of_int (68)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.PP.fst"
                                                     (Prims.of_int (112))
                                                     (Prims.of_int (50))
                                                     (Prims.of_int (112))
                                                     (Prims.of_int (68)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.PP.fst"
                                                           (Prims.of_int (112))
                                                           (Prims.of_int (57))
                                                           (Prims.of_int (112))
                                                           (Prims.of_int (61)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.PP.fst"
                                                           (Prims.of_int (112))
                                                           (Prims.of_int (50))
                                                           (Prims.of_int (112))
                                                           (Prims.of_int (68)))))
                                                  (Obj.magic (pp uu___1 y))
                                                  (fun uu___5 ->
                                                     (fun uu___5 ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (68)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (68)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (67)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (68)))))
                                                                   (Obj.magic
                                                                    (pp
                                                                    uu___2 z))
                                                                   (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    [uu___6]))))
                                                             (fun uu___6 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___7
                                                                    -> uu___5
                                                                    :: uu___6))))
                                                       uu___5)))
                                            (fun uu___5 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___6 -> uu___4 ::
                                                    uu___5)))) uu___4)))
                           (fun uu___4 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___5 ->
                                   FStar_Pprint.separate FStar_Pprint.comma
                                     uu___4))))
                     (fun uu___4 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___5 -> FStar_Pprint.parens uu___4)))
        }
let printable_tuple4 :
  'a 'b 'c 'd .
    'a printable ->
      'b printable ->
        'c printable -> 'd printable -> ('a * 'b * 'c * 'd) printable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          {
            pp =
              (fun uu___4 ->
                 match uu___4 with
                 | (x, y, z, w) ->
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.PP.fst"
                                (Prims.of_int (117)) (Prims.of_int (37))
                                (Prims.of_int (117)) (Prims.of_int (78)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.PP.fst"
                                (Prims.of_int (117)) (Prims.of_int (30))
                                (Prims.of_int (117)) (Prims.of_int (78)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.PP.fst"
                                      (Prims.of_int (117))
                                      (Prims.of_int (53))
                                      (Prims.of_int (117))
                                      (Prims.of_int (77)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.PP.fst"
                                      (Prims.of_int (117))
                                      (Prims.of_int (37))
                                      (Prims.of_int (117))
                                      (Prims.of_int (78)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Pulse.PP.fst"
                                            (Prims.of_int (117))
                                            (Prims.of_int (54))
                                            (Prims.of_int (117))
                                            (Prims.of_int (58)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Pulse.PP.fst"
                                            (Prims.of_int (117))
                                            (Prims.of_int (53))
                                            (Prims.of_int (117))
                                            (Prims.of_int (77)))))
                                   (Obj.magic (pp uu___ x))
                                   (fun uu___5 ->
                                      (fun uu___5 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.PP.fst"
                                                       (Prims.of_int (117))
                                                       (Prims.of_int (53))
                                                       (Prims.of_int (117))
                                                       (Prims.of_int (77)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.PP.fst"
                                                       (Prims.of_int (117))
                                                       (Prims.of_int (53))
                                                       (Prims.of_int (117))
                                                       (Prims.of_int (77)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.PP.fst"
                                                             (Prims.of_int (117))
                                                             (Prims.of_int (60))
                                                             (Prims.of_int (117))
                                                             (Prims.of_int (64)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.PP.fst"
                                                             (Prims.of_int (117))
                                                             (Prims.of_int (53))
                                                             (Prims.of_int (117))
                                                             (Prims.of_int (77)))))
                                                    (Obj.magic (pp uu___1 y))
                                                    (fun uu___6 ->
                                                       (fun uu___6 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (77)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (77)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (77)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___2 z))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (77)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (77)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___3 w))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    [uu___8]))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___7 ::
                                                                    uu___8))))
                                                                    uu___7)))
                                                               (fun uu___7 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___8 ->
                                                                    uu___6 ::
                                                                    uu___7))))
                                                         uu___6)))
                                              (fun uu___6 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___7 -> uu___5 ::
                                                      uu___6)))) uu___5)))
                             (fun uu___5 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___6 ->
                                     FStar_Pprint.separate FStar_Pprint.comma
                                       uu___5))))
                       (fun uu___5 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___6 -> FStar_Pprint.parens uu___5)))
          }