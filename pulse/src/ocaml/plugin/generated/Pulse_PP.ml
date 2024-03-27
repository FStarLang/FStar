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
  from_show Pulse_Show.tac_showable_string
let (printable_unit : unit printable) =
  from_show Pulse_Show.tac_showable_unit
let (printable_bool : Prims.bool printable) =
  from_show Pulse_Show.tac_showable_bool
let (printable_int : Prims.int printable) =
  from_show Pulse_Show.tac_showable_int
let (printable_ctag : Pulse_Syntax_Base.ctag printable) =
  from_show Pulse_Show.tac_showable_ctag
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
  from_show Pulse_Show.tac_showable_r_term
let (printable_st_term : Pulse_Syntax_Base.st_term printable) =
  from_show Pulse_Show.tac_showable_st_term
let (printable_universe : Pulse_Syntax_Base.universe printable) =
  from_show Pulse_Show.tac_showable_universe
let (printable_comp : Pulse_Syntax_Base.comp printable) =
  from_show Pulse_Show.tac_showable_comp
let (printable_env : Pulse_Typing_Env.env printable) =
  { pp = Pulse_Typing_Env.env_to_doc }
let (pp_effect_annot : Pulse_Syntax_Base.effect_annot printable) =
  from_show Pulse_Show.tac_showable_effect_annot
let (pp_record :
  (Prims.string * FStar_Pprint.document) Prims.list ->
    (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun flds ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (88))
               (Prims.of_int (4)) (Prims.of_int (88)) (Prims.of_int (104)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (90))
               (Prims.of_int (2)) (Prims.of_int (90)) (Prims.of_int (25)))))
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
                 (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (94))
                    (Prims.of_int (20)) (Prims.of_int (98))
                    (Prims.of_int (41)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (94))
                    (Prims.of_int (10)) (Prims.of_int (98))
                    (Prims.of_int (41)))))
           (Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.PP.fst"
                          (Prims.of_int (94)) (Prims.of_int (22))
                          (Prims.of_int (94)) (Prims.of_int (33)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.PP.fst"
                          (Prims.of_int (94)) (Prims.of_int (20))
                          (Prims.of_int (98)) (Prims.of_int (41)))))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.PP.fst"
                                (Prims.of_int (94)) (Prims.of_int (27))
                                (Prims.of_int (94)) (Prims.of_int (33)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.PP.fst"
                                (Prims.of_int (94)) (Prims.of_int (22))
                                (Prims.of_int (94)) (Prims.of_int (33)))))
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
                                     (Prims.of_int (94)) (Prims.of_int (20))
                                     (Prims.of_int (98)) (Prims.of_int (41)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.PP.fst"
                                     (Prims.of_int (94)) (Prims.of_int (20))
                                     (Prims.of_int (98)) (Prims.of_int (41)))))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "Pulse.PP.fst"
                                           (Prims.of_int (95))
                                           (Prims.of_int (22))
                                           (Prims.of_int (95))
                                           (Prims.of_int (55)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "Pulse.PP.fst"
                                           (Prims.of_int (94))
                                           (Prims.of_int (20))
                                           (Prims.of_int (98))
                                           (Prims.of_int (41)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.PP.fst"
                                                 (Prims.of_int (95))
                                                 (Prims.of_int (38))
                                                 (Prims.of_int (95))
                                                 (Prims.of_int (55)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.PP.fst"
                                                 (Prims.of_int (95))
                                                 (Prims.of_int (22))
                                                 (Prims.of_int (95))
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
                                                      (Prims.of_int (94))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (98))
                                                      (Prims.of_int (41)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.PP.fst"
                                                      (Prims.of_int (94))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (98))
                                                      (Prims.of_int (41)))))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.PP.fst"
                                                            (Prims.of_int (96))
                                                            (Prims.of_int (22))
                                                            (Prims.of_int (96))
                                                            (Prims.of_int (43)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.PP.fst"
                                                            (Prims.of_int (94))
                                                            (Prims.of_int (20))
                                                            (Prims.of_int (98))
                                                            (Prims.of_int (41)))))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.PP.fst"
                                                                  (Prims.of_int (96))
                                                                  (Prims.of_int (32))
                                                                  (Prims.of_int (96))
                                                                  (Prims.of_int (43)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.PP.fst"
                                                                  (Prims.of_int (96))
                                                                  (Prims.of_int (22))
                                                                  (Prims.of_int (96))
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
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (41)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (41)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (33)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (41)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (97))
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
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (98))
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
                 (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (103))
                    (Prims.of_int (31)) (Prims.of_int (103))
                    (Prims.of_int (60)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (103))
                    (Prims.of_int (17)) (Prims.of_int (103))
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
                            (Prims.of_int (108)) (Prims.of_int (29))
                            (Prims.of_int (108)) (Prims.of_int (53)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.PP.fst"
                            (Prims.of_int (108)) (Prims.of_int (22))
                            (Prims.of_int (108)) (Prims.of_int (53)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.PP.fst"
                                  (Prims.of_int (108)) (Prims.of_int (30))
                                  (Prims.of_int (108)) (Prims.of_int (34)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.PP.fst"
                                  (Prims.of_int (108)) (Prims.of_int (29))
                                  (Prims.of_int (108)) (Prims.of_int (53)))))
                         (Obj.magic (pp uu___ x))
                         (fun uu___3 ->
                            (fun uu___3 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.PP.fst"
                                             (Prims.of_int (108))
                                             (Prims.of_int (38))
                                             (Prims.of_int (108))
                                             (Prims.of_int (52)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.PP.fst"
                                             (Prims.of_int (108))
                                             (Prims.of_int (29))
                                             (Prims.of_int (108))
                                             (Prims.of_int (53)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.PP.fst"
                                                   (Prims.of_int (108))
                                                   (Prims.of_int (48))
                                                   (Prims.of_int (108))
                                                   (Prims.of_int (52)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.PP.fst"
                                                   (Prims.of_int (108))
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (108))
                                                   (Prims.of_int (52)))))
                                          (Obj.magic (pp uu___1 y))
                                          (fun uu___4 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___5 ->
                                                  FStar_Pprint.op_Hat_Slash_Hat
                                                    FStar_Pprint.comma uu___4))))
                                    (fun uu___4 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___5 ->
                                            FStar_Pprint.op_Hat_Hat uu___3
                                              uu___4)))) uu___3)))
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
                              (Prims.of_int (113)) (Prims.of_int (32))
                              (Prims.of_int (113)) (Prims.of_int (74)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.PP.fst"
                              (Prims.of_int (113)) (Prims.of_int (25))
                              (Prims.of_int (113)) (Prims.of_int (74)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.PP.fst"
                                    (Prims.of_int (113)) (Prims.of_int (33))
                                    (Prims.of_int (113)) (Prims.of_int (37)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.PP.fst"
                                    (Prims.of_int (113)) (Prims.of_int (32))
                                    (Prims.of_int (113)) (Prims.of_int (74)))))
                           (Obj.magic (pp uu___ x))
                           (fun uu___4 ->
                              (fun uu___4 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.PP.fst"
                                               (Prims.of_int (113))
                                               (Prims.of_int (41))
                                               (Prims.of_int (113))
                                               (Prims.of_int (73)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.PP.fst"
                                               (Prims.of_int (113))
                                               (Prims.of_int (32))
                                               (Prims.of_int (113))
                                               (Prims.of_int (74)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.PP.fst"
                                                     (Prims.of_int (113))
                                                     (Prims.of_int (51))
                                                     (Prims.of_int (113))
                                                     (Prims.of_int (73)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.PP.fst"
                                                     (Prims.of_int (113))
                                                     (Prims.of_int (41))
                                                     (Prims.of_int (113))
                                                     (Prims.of_int (73)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.PP.fst"
                                                           (Prims.of_int (113))
                                                           (Prims.of_int (51))
                                                           (Prims.of_int (113))
                                                           (Prims.of_int (55)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.PP.fst"
                                                           (Prims.of_int (113))
                                                           (Prims.of_int (51))
                                                           (Prims.of_int (113))
                                                           (Prims.of_int (73)))))
                                                  (Obj.magic (pp uu___1 y))
                                                  (fun uu___5 ->
                                                     (fun uu___5 ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (73)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (73)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (73)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (73)))))
                                                                   (Obj.magic
                                                                    (pp
                                                                    uu___2 z))
                                                                   (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___6))))
                                                             (fun uu___6 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___7
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___5
                                                                    uu___6))))
                                                       uu___5)))
                                            (fun uu___5 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___6 ->
                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                      FStar_Pprint.comma
                                                      uu___5))))
                                      (fun uu___5 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___6 ->
                                              FStar_Pprint.op_Hat_Hat uu___4
                                                uu___5)))) uu___4)))
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
                                (Prims.of_int (118)) (Prims.of_int (35))
                                (Prims.of_int (118)) (Prims.of_int (95)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.PP.fst"
                                (Prims.of_int (118)) (Prims.of_int (28))
                                (Prims.of_int (118)) (Prims.of_int (95)))))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.PP.fst"
                                      (Prims.of_int (118))
                                      (Prims.of_int (36))
                                      (Prims.of_int (118))
                                      (Prims.of_int (40)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.PP.fst"
                                      (Prims.of_int (118))
                                      (Prims.of_int (35))
                                      (Prims.of_int (118))
                                      (Prims.of_int (95)))))
                             (Obj.magic (pp uu___ x))
                             (fun uu___5 ->
                                (fun uu___5 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.PP.fst"
                                                 (Prims.of_int (118))
                                                 (Prims.of_int (44))
                                                 (Prims.of_int (118))
                                                 (Prims.of_int (94)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.PP.fst"
                                                 (Prims.of_int (118))
                                                 (Prims.of_int (35))
                                                 (Prims.of_int (118))
                                                 (Prims.of_int (95)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.PP.fst"
                                                       (Prims.of_int (118))
                                                       (Prims.of_int (54))
                                                       (Prims.of_int (118))
                                                       (Prims.of_int (94)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.PP.fst"
                                                       (Prims.of_int (118))
                                                       (Prims.of_int (44))
                                                       (Prims.of_int (118))
                                                       (Prims.of_int (94)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.PP.fst"
                                                             (Prims.of_int (118))
                                                             (Prims.of_int (54))
                                                             (Prims.of_int (118))
                                                             (Prims.of_int (58)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.PP.fst"
                                                             (Prims.of_int (118))
                                                             (Prims.of_int (54))
                                                             (Prims.of_int (118))
                                                             (Prims.of_int (94)))))
                                                    (Obj.magic (pp uu___1 y))
                                                    (fun uu___6 ->
                                                       (fun uu___6 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (94)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (94)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (94)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (94)))))
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
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (94)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (94)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___3 w))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___7
                                                                    uu___8))))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___7))))
                                                               (fun uu___7 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___8 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___6
                                                                    uu___7))))
                                                         uu___6)))
                                              (fun uu___6 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___7 ->
                                                      FStar_Pprint.op_Hat_Slash_Hat
                                                        FStar_Pprint.comma
                                                        uu___6))))
                                        (fun uu___6 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___7 ->
                                                FStar_Pprint.op_Hat_Hat
                                                  uu___5 uu___6)))) uu___5)))
                       (fun uu___5 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___6 -> FStar_Pprint.parens uu___5)))
          }
let printable_tuple5 :
  'a 'b 'c 'd 'e .
    'a printable ->
      'b printable ->
        'c printable ->
          'd printable -> 'e printable -> ('a * 'b * 'c * 'd * 'e) printable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            {
              pp =
                (fun uu___5 ->
                   match uu___5 with
                   | (x, y, z, w, v) ->
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.PP.fst"
                                  (Prims.of_int (123)) (Prims.of_int (38))
                                  (Prims.of_int (123)) (Prims.of_int (116)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.PP.fst"
                                  (Prims.of_int (123)) (Prims.of_int (31))
                                  (Prims.of_int (123)) (Prims.of_int (116)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.PP.fst"
                                        (Prims.of_int (123))
                                        (Prims.of_int (39))
                                        (Prims.of_int (123))
                                        (Prims.of_int (43)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.PP.fst"
                                        (Prims.of_int (123))
                                        (Prims.of_int (38))
                                        (Prims.of_int (123))
                                        (Prims.of_int (116)))))
                               (Obj.magic (pp uu___ x))
                               (fun uu___6 ->
                                  (fun uu___6 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.PP.fst"
                                                   (Prims.of_int (123))
                                                   (Prims.of_int (47))
                                                   (Prims.of_int (123))
                                                   (Prims.of_int (115)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.PP.fst"
                                                   (Prims.of_int (123))
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (123))
                                                   (Prims.of_int (116)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.PP.fst"
                                                         (Prims.of_int (123))
                                                         (Prims.of_int (57))
                                                         (Prims.of_int (123))
                                                         (Prims.of_int (115)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.PP.fst"
                                                         (Prims.of_int (123))
                                                         (Prims.of_int (47))
                                                         (Prims.of_int (123))
                                                         (Prims.of_int (115)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.PP.fst"
                                                               (Prims.of_int (123))
                                                               (Prims.of_int (57))
                                                               (Prims.of_int (123))
                                                               (Prims.of_int (61)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.PP.fst"
                                                               (Prims.of_int (123))
                                                               (Prims.of_int (57))
                                                               (Prims.of_int (123))
                                                               (Prims.of_int (115)))))
                                                      (Obj.magic
                                                         (pp uu___1 y))
                                                      (fun uu___7 ->
                                                         (fun uu___7 ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___2 z))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___3 w))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___4 v))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___10))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___9
                                                                    uu___10))))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___9))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___8
                                                                    uu___9))))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___8))))
                                                                 (fun uu___8
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___7
                                                                    uu___8))))
                                                           uu___7)))
                                                (fun uu___7 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___8 ->
                                                        FStar_Pprint.op_Hat_Slash_Hat
                                                          FStar_Pprint.comma
                                                          uu___7))))
                                          (fun uu___7 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___8 ->
                                                  FStar_Pprint.op_Hat_Hat
                                                    uu___6 uu___7)))) uu___6)))
                         (fun uu___6 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___7 -> FStar_Pprint.parens uu___6)))
            }
let printable_tuple6 :
  'a 'b 'c 'd 'e 'f .
    'a printable ->
      'b printable ->
        'c printable ->
          'd printable ->
            'e printable ->
              'f printable -> ('a * 'b * 'c * 'd * 'e * 'f) printable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            fun uu___5 ->
              {
                pp =
                  (fun uu___6 ->
                     match uu___6 with
                     | (x, y, z, w, v, u) ->
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.PP.fst"
                                    (Prims.of_int (128)) (Prims.of_int (41))
                                    (Prims.of_int (128)) (Prims.of_int (137)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.PP.fst"
                                    (Prims.of_int (128)) (Prims.of_int (34))
                                    (Prims.of_int (128)) (Prims.of_int (137)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Pulse.PP.fst"
                                          (Prims.of_int (128))
                                          (Prims.of_int (42))
                                          (Prims.of_int (128))
                                          (Prims.of_int (46)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Pulse.PP.fst"
                                          (Prims.of_int (128))
                                          (Prims.of_int (41))
                                          (Prims.of_int (128))
                                          (Prims.of_int (137)))))
                                 (Obj.magic (pp uu___ x))
                                 (fun uu___7 ->
                                    (fun uu___7 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.PP.fst"
                                                     (Prims.of_int (128))
                                                     (Prims.of_int (50))
                                                     (Prims.of_int (128))
                                                     (Prims.of_int (136)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.PP.fst"
                                                     (Prims.of_int (128))
                                                     (Prims.of_int (41))
                                                     (Prims.of_int (128))
                                                     (Prims.of_int (137)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.PP.fst"
                                                           (Prims.of_int (128))
                                                           (Prims.of_int (60))
                                                           (Prims.of_int (128))
                                                           (Prims.of_int (136)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.PP.fst"
                                                           (Prims.of_int (128))
                                                           (Prims.of_int (50))
                                                           (Prims.of_int (128))
                                                           (Prims.of_int (136)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.PP.fst"
                                                                 (Prims.of_int (128))
                                                                 (Prims.of_int (60))
                                                                 (Prims.of_int (128))
                                                                 (Prims.of_int (64)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.PP.fst"
                                                                 (Prims.of_int (128))
                                                                 (Prims.of_int (60))
                                                                 (Prims.of_int (128))
                                                                 (Prims.of_int (136)))))
                                                        (Obj.magic
                                                           (pp uu___1 y))
                                                        (fun uu___8 ->
                                                           (fun uu___8 ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___2 z))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (100)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___3 w))
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
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (118)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___4 v))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___5 u))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___12))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___11
                                                                    uu___12))))
                                                                    uu___11)))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___11))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___10
                                                                    uu___11))))
                                                                    uu___10)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___10))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___9
                                                                    uu___10))))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___9))))
                                                                   (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___8
                                                                    uu___9))))
                                                             uu___8)))
                                                  (fun uu___8 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___9 ->
                                                          FStar_Pprint.op_Hat_Slash_Hat
                                                            FStar_Pprint.comma
                                                            uu___8))))
                                            (fun uu___8 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___9 ->
                                                    FStar_Pprint.op_Hat_Hat
                                                      uu___7 uu___8))))
                                      uu___7)))
                           (fun uu___7 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___8 -> FStar_Pprint.parens uu___7)))
              }
let printable_tuple7 :
  'a 'b 'c 'd 'e 'f 'g .
    'a printable ->
      'b printable ->
        'c printable ->
          'd printable ->
            'e printable ->
              'f printable ->
                'g printable -> ('a * 'b * 'c * 'd * 'e * 'f * 'g) printable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            fun uu___5 ->
              fun uu___6 ->
                {
                  pp =
                    (fun uu___7 ->
                       match uu___7 with
                       | (x, y, z, w, v, u, t) ->
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.PP.fst"
                                      (Prims.of_int (133))
                                      (Prims.of_int (44))
                                      (Prims.of_int (133))
                                      (Prims.of_int (158)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Pulse.PP.fst"
                                      (Prims.of_int (133))
                                      (Prims.of_int (37))
                                      (Prims.of_int (133))
                                      (Prims.of_int (158)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Pulse.PP.fst"
                                            (Prims.of_int (133))
                                            (Prims.of_int (45))
                                            (Prims.of_int (133))
                                            (Prims.of_int (49)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Pulse.PP.fst"
                                            (Prims.of_int (133))
                                            (Prims.of_int (44))
                                            (Prims.of_int (133))
                                            (Prims.of_int (158)))))
                                   (Obj.magic (pp uu___ x))
                                   (fun uu___8 ->
                                      (fun uu___8 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.PP.fst"
                                                       (Prims.of_int (133))
                                                       (Prims.of_int (53))
                                                       (Prims.of_int (133))
                                                       (Prims.of_int (157)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.PP.fst"
                                                       (Prims.of_int (133))
                                                       (Prims.of_int (44))
                                                       (Prims.of_int (133))
                                                       (Prims.of_int (158)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.PP.fst"
                                                             (Prims.of_int (133))
                                                             (Prims.of_int (63))
                                                             (Prims.of_int (133))
                                                             (Prims.of_int (157)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.PP.fst"
                                                             (Prims.of_int (133))
                                                             (Prims.of_int (53))
                                                             (Prims.of_int (133))
                                                             (Prims.of_int (157)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.PP.fst"
                                                                   (Prims.of_int (133))
                                                                   (Prims.of_int (63))
                                                                   (Prims.of_int (133))
                                                                   (Prims.of_int (67)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.PP.fst"
                                                                   (Prims.of_int (133))
                                                                   (Prims.of_int (63))
                                                                   (Prims.of_int (133))
                                                                   (Prims.of_int (157)))))
                                                          (Obj.magic
                                                             (pp uu___1 y))
                                                          (fun uu___9 ->
                                                             (fun uu___9 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___2 z))
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
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (103)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___3 w))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (121)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___4 v))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (139)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___5 u))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (135))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                    (Obj.magic
                                                                    (pp
                                                                    uu___6 t))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___14))))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___13
                                                                    uu___14))))
                                                                    uu___13)))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___13))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___12
                                                                    uu___13))))
                                                                    uu___12)))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___12))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___11
                                                                    uu___12))))
                                                                    uu___11)))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___11))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___10
                                                                    uu___11))))
                                                                    uu___10)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    FStar_Pprint.comma
                                                                    uu___10))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___9
                                                                    uu___10))))
                                                               uu___9)))
                                                    (fun uu___9 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___10 ->
                                                            FStar_Pprint.op_Hat_Slash_Hat
                                                              FStar_Pprint.comma
                                                              uu___9))))
                                              (fun uu___9 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___10 ->
                                                      FStar_Pprint.op_Hat_Hat
                                                        uu___8 uu___9))))
                                        uu___8)))
                             (fun uu___8 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___9 -> FStar_Pprint.parens uu___8)))
                }