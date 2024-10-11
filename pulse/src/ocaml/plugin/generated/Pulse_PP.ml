open Prims
let (text : Prims.string -> FStarC_Pprint.document) =
  fun s ->
    FStarC_Pprint.flow (FStarC_Pprint.break_ Prims.int_one)
      (FStarC_Pprint.words s)
let (indent : FStarC_Pprint.document -> FStarC_Pprint.document) =
  fun d ->
    FStarC_Pprint.nest (Prims.of_int (2))
      (FStarC_Pprint.op_Hat_Hat FStarC_Pprint.hardline (FStarC_Pprint.align d))
type 'a printable =
  {
  pp: 'a -> (FStarC_Pprint.document, unit) FStar_Tactics_Effect.tac_repr }
let __proj__Mkprintable__item__pp :
  'a .
    'a printable ->
      'a -> (FStarC_Pprint.document, unit) FStar_Tactics_Effect.tac_repr
  = fun projectee -> match projectee with | { pp;_} -> pp
let pp :
  'a .
    'a printable ->
      'a -> (FStarC_Pprint.document, unit) FStar_Tactics_Effect.tac_repr
  = fun projectee -> match projectee with | { pp = pp1;_} -> pp1
let show_from_pp : 'a . 'a printable -> 'a Pulse_Show.tac_showable =
  fun d ->
    {
      Pulse_Show.show =
        (fun x ->
           let uu___ = pp d x in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (47))
                      (Prims.of_int (26)) (Prims.of_int (47))
                      (Prims.of_int (32)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (47))
                      (Prims.of_int (19)) (Prims.of_int (47))
                      (Prims.of_int (32))))) (Obj.magic uu___)
             (fun uu___1 ->
                FStar_Tactics_Effect.lift_div_tac
                  (fun uu___2 -> FStarC_Pprint.render uu___1)))
    }
let from_show : 'a . 'a Pulse_Show.tac_showable -> 'a printable =
  fun d ->
    {
      pp =
        (fun x ->
           let uu___ = Pulse_Show.show d x in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (52))
                      (Prims.of_int (34)) (Prims.of_int (52))
                      (Prims.of_int (42)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (52))
                      (Prims.of_int (17)) (Prims.of_int (52))
                      (Prims.of_int (42))))) (Obj.magic uu___)
             (fun uu___1 ->
                FStar_Tactics_Effect.lift_div_tac
                  (fun uu___2 -> FStarC_Pprint.arbitrary_string uu___1)))
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
                          (fun uu___2 -> FStarC_Pprint.doc_of_string "None")))
              | FStar_Pervasives_Native.Some v ->
                  Obj.magic
                    (Obj.repr
                       (let uu___2 = pp uu___ v in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.PP.fst"
                                   (Prims.of_int (64)) (Prims.of_int (54))
                                   (Prims.of_int (64)) (Prims.of_int (58)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.PP.fst"
                                   (Prims.of_int (64)) (Prims.of_int (29))
                                   (Prims.of_int (64)) (Prims.of_int (58)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 ->
                                  FStarC_Pprint.op_Hat_Slash_Hat
                                    (FStarC_Pprint.doc_of_string "Some")
                                    uu___3))))) uu___1)
    }
let rec separate_map :
  'a .
    FStarC_Pprint.document ->
      ('a -> (FStarC_Pprint.document, unit) FStar_Tactics_Effect.tac_repr) ->
        'a Prims.list ->
          (FStarC_Pprint.document, unit) FStar_Tactics_Effect.tac_repr
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
                           (fun uu___ -> FStarC_Pprint.empty)))
               | x::[] -> Obj.magic (Obj.repr (f x))
               | x::xs ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = f x in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.PP.fst"
                                    (Prims.of_int (73)) (Prims.of_int (13))
                                    (Prims.of_int (73)) (Prims.of_int (16)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.PP.fst"
                                    (Prims.of_int (73)) (Prims.of_int (13))
                                    (Prims.of_int (73)) (Prims.of_int (49)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 let uu___2 =
                                   let uu___3 = separate_map sep f xs in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.PP.fst"
                                              (Prims.of_int (73))
                                              (Prims.of_int (28))
                                              (Prims.of_int (73))
                                              (Prims.of_int (49)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.PP.fst"
                                              (Prims.of_int (73))
                                              (Prims.of_int (20))
                                              (Prims.of_int (73))
                                              (Prims.of_int (49)))))
                                     (Obj.magic uu___3)
                                     (fun uu___4 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___5 ->
                                             FStarC_Pprint.op_Hat_Slash_Hat
                                               sep uu___4)) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.PP.fst"
                                               (Prims.of_int (73))
                                               (Prims.of_int (20))
                                               (Prims.of_int (73))
                                               (Prims.of_int (49)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.PP.fst"
                                               (Prims.of_int (73))
                                               (Prims.of_int (13))
                                               (Prims.of_int (73))
                                               (Prims.of_int (49)))))
                                      (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              FStarC_Pprint.op_Hat_Hat uu___1
                                                uu___3)))) uu___1)))) uu___2
          uu___1 uu___
let printable_list : 'a . 'a printable -> 'a Prims.list printable =
  fun uu___ ->
    {
      pp =
        (fun l ->
           let uu___1 = separate_map FStarC_Pprint.comma (pp uu___) l in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (76))
                      (Prims.of_int (26)) (Prims.of_int (76))
                      (Prims.of_int (51)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (76))
                      (Prims.of_int (17)) (Prims.of_int (76))
                      (Prims.of_int (51))))) (Obj.magic uu___1)
             (fun uu___2 ->
                FStar_Tactics_Effect.lift_div_tac
                  (fun uu___3 -> FStarC_Pprint.brackets uu___2)))
    }
let (printable_term : Pulse_Syntax_Base.term printable) =
  { pp = Pulse_Syntax_Printer.term_to_doc }
let (printable_binder : Pulse_Syntax_Base.binder printable) =
  { pp = Pulse_Syntax_Printer.binder_to_doc }
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
  (Prims.string * FStarC_Pprint.document) Prims.list ->
    (FStarC_Pprint.document, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun flds ->
    let uu___ =
      separate_map (FStarC_Pprint.doc_of_string ";")
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      match uu___1 with
                      | (s, d) ->
                          FStarC_Pprint.group
                            (FStarC_Pprint.op_Hat_Slash_Hat
                               (FStarC_Pprint.doc_of_string s)
                               (FStarC_Pprint.op_Hat_Slash_Hat
                                  FStarC_Pprint.equals (FStarC_Pprint.group d))))))
             uu___1) flds in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (93))
               (Prims.of_int (4)) (Prims.of_int (93)) (Prims.of_int (104)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (95))
               (Prims.of_int (2)) (Prims.of_int (95)) (Prims.of_int (25)))))
      (Obj.magic uu___)
      (fun flds_doc ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStarC_Pprint.braces (FStarC_Pprint.align flds_doc)))
let (printable_post_hint_t : Pulse_Typing.post_hint_t printable) =
  {
    pp =
      (fun h ->
         let uu___ =
           let uu___1 =
             let uu___2 = pp printable_env h.Pulse_Typing.g in
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (99))
                        (Prims.of_int (27)) (Prims.of_int (99))
                        (Prims.of_int (33)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (99))
                        (Prims.of_int (22)) (Prims.of_int (99))
                        (Prims.of_int (33))))) (Obj.magic uu___2)
               (fun uu___3 ->
                  FStar_Tactics_Effect.lift_div_tac
                    (fun uu___4 -> ("g", uu___3))) in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (99))
                      (Prims.of_int (22)) (Prims.of_int (99))
                      (Prims.of_int (33)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (99))
                      (Prims.of_int (20)) (Prims.of_int (103))
                      (Prims.of_int (41))))) (Obj.magic uu___1)
             (fun uu___2 ->
                (fun uu___2 ->
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         pp pp_effect_annot h.Pulse_Typing.effect_annot in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.PP.fst"
                                  (Prims.of_int (100)) (Prims.of_int (38))
                                  (Prims.of_int (100)) (Prims.of_int (55)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.PP.fst"
                                  (Prims.of_int (100)) (Prims.of_int (22))
                                  (Prims.of_int (100)) (Prims.of_int (55)))))
                         (Obj.magic uu___5)
                         (fun uu___6 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___7 -> ("effect_annot", uu___6))) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.PP.fst"
                                (Prims.of_int (100)) (Prims.of_int (22))
                                (Prims.of_int (100)) (Prims.of_int (55)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.PP.fst"
                                (Prims.of_int (99)) (Prims.of_int (20))
                                (Prims.of_int (103)) (Prims.of_int (41)))))
                       (Obj.magic uu___4)
                       (fun uu___5 ->
                          (fun uu___5 ->
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   pp printable_term h.Pulse_Typing.ret_ty in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Pulse.PP.fst"
                                            (Prims.of_int (101))
                                            (Prims.of_int (32))
                                            (Prims.of_int (101))
                                            (Prims.of_int (43)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Pulse.PP.fst"
                                            (Prims.of_int (101))
                                            (Prims.of_int (22))
                                            (Prims.of_int (101))
                                            (Prims.of_int (43)))))
                                   (Obj.magic uu___8)
                                   (fun uu___9 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___10 -> ("ret_ty", uu___9))) in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Pulse.PP.fst"
                                          (Prims.of_int (101))
                                          (Prims.of_int (22))
                                          (Prims.of_int (101))
                                          (Prims.of_int (43)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Pulse.PP.fst"
                                          (Prims.of_int (99))
                                          (Prims.of_int (20))
                                          (Prims.of_int (103))
                                          (Prims.of_int (41)))))
                                 (Obj.magic uu___7)
                                 (fun uu___8 ->
                                    (fun uu___8 ->
                                       let uu___9 =
                                         let uu___10 =
                                           let uu___11 =
                                             pp printable_universe
                                               h.Pulse_Typing.u in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.PP.fst"
                                                      (Prims.of_int (102))
                                                      (Prims.of_int (27))
                                                      (Prims.of_int (102))
                                                      (Prims.of_int (33)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.PP.fst"
                                                      (Prims.of_int (102))
                                                      (Prims.of_int (22))
                                                      (Prims.of_int (102))
                                                      (Prims.of_int (33)))))
                                             (Obj.magic uu___11)
                                             (fun uu___12 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___13 ->
                                                     ("u", uu___12))) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.PP.fst"
                                                    (Prims.of_int (102))
                                                    (Prims.of_int (22))
                                                    (Prims.of_int (102))
                                                    (Prims.of_int (33)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.PP.fst"
                                                    (Prims.of_int (99))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (103))
                                                    (Prims.of_int (41)))))
                                           (Obj.magic uu___10)
                                           (fun uu___11 ->
                                              (fun uu___11 ->
                                                 let uu___12 =
                                                   let uu___13 =
                                                     let uu___14 =
                                                       pp printable_term
                                                         h.Pulse_Typing.post in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.PP.fst"
                                                                (Prims.of_int (103))
                                                                (Prims.of_int (30))
                                                                (Prims.of_int (103))
                                                                (Prims.of_int (39)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.PP.fst"
                                                                (Prims.of_int (103))
                                                                (Prims.of_int (22))
                                                                (Prims.of_int (103))
                                                                (Prims.of_int (39)))))
                                                       (Obj.magic uu___14)
                                                       (fun uu___15 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___16 ->
                                                               ("post",
                                                                 uu___15))) in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.PP.fst"
                                                              (Prims.of_int (103))
                                                              (Prims.of_int (22))
                                                              (Prims.of_int (103))
                                                              (Prims.of_int (39)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.PP.fst"
                                                              (Prims.of_int (99))
                                                              (Prims.of_int (20))
                                                              (Prims.of_int (103))
                                                              (Prims.of_int (41)))))
                                                     (Obj.magic uu___13)
                                                     (fun uu___14 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___15 ->
                                                             [uu___14])) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.PP.fst"
                                                               (Prims.of_int (99))
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (103))
                                                               (Prims.of_int (41)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.PP.fst"
                                                               (Prims.of_int (99))
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (103))
                                                               (Prims.of_int (41)))))
                                                      (Obj.magic uu___12)
                                                      (fun uu___13 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___14 ->
                                                              uu___11 ::
                                                              uu___13))))
                                                uu___11) in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.PP.fst"
                                                     (Prims.of_int (99))
                                                     (Prims.of_int (20))
                                                     (Prims.of_int (103))
                                                     (Prims.of_int (41)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.PP.fst"
                                                     (Prims.of_int (99))
                                                     (Prims.of_int (20))
                                                     (Prims.of_int (103))
                                                     (Prims.of_int (41)))))
                                            (Obj.magic uu___9)
                                            (fun uu___10 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___11 -> uu___8 ::
                                                    uu___10)))) uu___8) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "Pulse.PP.fst"
                                           (Prims.of_int (99))
                                           (Prims.of_int (20))
                                           (Prims.of_int (103))
                                           (Prims.of_int (41)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "Pulse.PP.fst"
                                           (Prims.of_int (99))
                                           (Prims.of_int (20))
                                           (Prims.of_int (103))
                                           (Prims.of_int (41)))))
                                  (Obj.magic uu___6)
                                  (fun uu___7 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___8 -> uu___5 :: uu___7))))
                            uu___5) in
                   Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.PP.fst"
                                 (Prims.of_int (99)) (Prims.of_int (20))
                                 (Prims.of_int (103)) (Prims.of_int (41)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.PP.fst"
                                 (Prims.of_int (99)) (Prims.of_int (20))
                                 (Prims.of_int (103)) (Prims.of_int (41)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___5 -> uu___2 :: uu___4)))) uu___2) in
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (99))
                    (Prims.of_int (20)) (Prims.of_int (103))
                    (Prims.of_int (41)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.PP.fst" (Prims.of_int (99))
                    (Prims.of_int (10)) (Prims.of_int (103))
                    (Prims.of_int (41))))) (Obj.magic uu___)
           (fun uu___1 -> (fun uu___1 -> Obj.magic (pp_record uu___1)) uu___1))
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
                 let uu___3 =
                   let uu___4 = pp uu___ x in
                   FStar_Tactics_Effect.tac_bind
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
                     (Obj.magic uu___4)
                     (fun uu___5 ->
                        (fun uu___5 ->
                           let uu___6 =
                             let uu___7 = pp uu___1 y in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.PP.fst"
                                        (Prims.of_int (108))
                                        (Prims.of_int (48))
                                        (Prims.of_int (108))
                                        (Prims.of_int (52)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.PP.fst"
                                        (Prims.of_int (108))
                                        (Prims.of_int (38))
                                        (Prims.of_int (108))
                                        (Prims.of_int (52)))))
                               (Obj.magic uu___7)
                               (fun uu___8 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___9 ->
                                       FStarC_Pprint.op_Hat_Slash_Hat
                                         FStarC_Pprint.comma uu___8)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Pulse.PP.fst"
                                         (Prims.of_int (108))
                                         (Prims.of_int (38))
                                         (Prims.of_int (108))
                                         (Prims.of_int (52)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Pulse.PP.fst"
                                         (Prims.of_int (108))
                                         (Prims.of_int (29))
                                         (Prims.of_int (108))
                                         (Prims.of_int (53)))))
                                (Obj.magic uu___6)
                                (fun uu___7 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___8 ->
                                        FStarC_Pprint.op_Hat_Hat uu___5 uu___7))))
                          uu___5) in
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
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___5 -> FStarC_Pprint.parens uu___4)))
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
                   let uu___4 =
                     let uu___5 = pp uu___ x in
                     FStar_Tactics_Effect.tac_bind
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
                       (Obj.magic uu___5)
                       (fun uu___6 ->
                          (fun uu___6 ->
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 = pp uu___1 y in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Pulse.PP.fst"
                                            (Prims.of_int (113))
                                            (Prims.of_int (51))
                                            (Prims.of_int (113))
                                            (Prims.of_int (55)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Pulse.PP.fst"
                                            (Prims.of_int (113))
                                            (Prims.of_int (51))
                                            (Prims.of_int (113))
                                            (Prims.of_int (73)))))
                                   (Obj.magic uu___9)
                                   (fun uu___10 ->
                                      (fun uu___10 ->
                                         let uu___11 =
                                           let uu___12 = pp uu___2 z in
                                           FStar_Tactics_Effect.tac_bind
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
                                             (Obj.magic uu___12)
                                             (fun uu___13 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___14 ->
                                                     FStarC_Pprint.op_Hat_Slash_Hat
                                                       FStarC_Pprint.comma
                                                       uu___13)) in
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
                                              (Obj.magic uu___11)
                                              (fun uu___12 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___13 ->
                                                      FStarC_Pprint.op_Hat_Hat
                                                        uu___10 uu___12))))
                                        uu___10) in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Pulse.PP.fst"
                                          (Prims.of_int (113))
                                          (Prims.of_int (51))
                                          (Prims.of_int (113))
                                          (Prims.of_int (73)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Pulse.PP.fst"
                                          (Prims.of_int (113))
                                          (Prims.of_int (41))
                                          (Prims.of_int (113))
                                          (Prims.of_int (73)))))
                                 (Obj.magic uu___8)
                                 (fun uu___9 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___10 ->
                                         FStarC_Pprint.op_Hat_Slash_Hat
                                           FStarC_Pprint.comma uu___9)) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "Pulse.PP.fst"
                                           (Prims.of_int (113))
                                           (Prims.of_int (41))
                                           (Prims.of_int (113))
                                           (Prims.of_int (73)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "Pulse.PP.fst"
                                           (Prims.of_int (113))
                                           (Prims.of_int (32))
                                           (Prims.of_int (113))
                                           (Prims.of_int (74)))))
                                  (Obj.magic uu___7)
                                  (fun uu___8 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___9 ->
                                          FStarC_Pprint.op_Hat_Hat uu___6
                                            uu___8)))) uu___6) in
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
                     (Obj.magic uu___4)
                     (fun uu___5 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___6 -> FStarC_Pprint.parens uu___5)))
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
                     let uu___5 =
                       let uu___6 = pp uu___ x in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.PP.fst"
                                  (Prims.of_int (118)) (Prims.of_int (36))
                                  (Prims.of_int (118)) (Prims.of_int (40)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.PP.fst"
                                  (Prims.of_int (118)) (Prims.of_int (35))
                                  (Prims.of_int (118)) (Prims.of_int (95)))))
                         (Obj.magic uu___6)
                         (fun uu___7 ->
                            (fun uu___7 ->
                               let uu___8 =
                                 let uu___9 =
                                   let uu___10 = pp uu___1 y in
                                   FStar_Tactics_Effect.tac_bind
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
                                     (Obj.magic uu___10)
                                     (fun uu___11 ->
                                        (fun uu___11 ->
                                           let uu___12 =
                                             let uu___13 =
                                               let uu___14 = pp uu___2 z in
                                               FStar_Tactics_Effect.tac_bind
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
                                                 (Obj.magic uu___14)
                                                 (fun uu___15 ->
                                                    (fun uu___15 ->
                                                       let uu___16 =
                                                         let uu___17 =
                                                           pp uu___3 w in
                                                         FStar_Tactics_Effect.tac_bind
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
                                                           (Obj.magic uu___17)
                                                           (fun uu___18 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___19
                                                                   ->
                                                                   FStarC_Pprint.op_Hat_Slash_Hat
                                                                    FStarC_Pprint.comma
                                                                    uu___18)) in
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
                                                               uu___16)
                                                            (fun uu___17 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___18
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___15
                                                                    uu___17))))
                                                      uu___15) in
                                             FStar_Tactics_Effect.tac_bind
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
                                               (Obj.magic uu___13)
                                               (fun uu___14 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___15 ->
                                                       FStarC_Pprint.op_Hat_Slash_Hat
                                                         FStarC_Pprint.comma
                                                         uu___14)) in
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
                                                (Obj.magic uu___12)
                                                (fun uu___13 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___14 ->
                                                        FStarC_Pprint.op_Hat_Hat
                                                          uu___11 uu___13))))
                                          uu___11) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Pulse.PP.fst"
                                            (Prims.of_int (118))
                                            (Prims.of_int (54))
                                            (Prims.of_int (118))
                                            (Prims.of_int (94)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Pulse.PP.fst"
                                            (Prims.of_int (118))
                                            (Prims.of_int (44))
                                            (Prims.of_int (118))
                                            (Prims.of_int (94)))))
                                   (Obj.magic uu___9)
                                   (fun uu___10 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___11 ->
                                           FStarC_Pprint.op_Hat_Slash_Hat
                                             FStarC_Pprint.comma uu___10)) in
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
                                    (Obj.magic uu___8)
                                    (fun uu___9 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___10 ->
                                            FStarC_Pprint.op_Hat_Hat uu___7
                                              uu___9)))) uu___7) in
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
                       (Obj.magic uu___5)
                       (fun uu___6 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___7 -> FStarC_Pprint.parens uu___6)))
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
                       let uu___6 =
                         let uu___7 = pp uu___ x in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.PP.fst"
                                    (Prims.of_int (123)) (Prims.of_int (39))
                                    (Prims.of_int (123)) (Prims.of_int (43)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.PP.fst"
                                    (Prims.of_int (123)) (Prims.of_int (38))
                                    (Prims.of_int (123)) (Prims.of_int (116)))))
                           (Obj.magic uu___7)
                           (fun uu___8 ->
                              (fun uu___8 ->
                                 let uu___9 =
                                   let uu___10 =
                                     let uu___11 = pp uu___1 y in
                                     FStar_Tactics_Effect.tac_bind
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
                                       (Obj.magic uu___11)
                                       (fun uu___12 ->
                                          (fun uu___12 ->
                                             let uu___13 =
                                               let uu___14 =
                                                 let uu___15 = pp uu___2 z in
                                                 FStar_Tactics_Effect.tac_bind
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
                                                   (Obj.magic uu___15)
                                                   (fun uu___16 ->
                                                      (fun uu___16 ->
                                                         let uu___17 =
                                                           let uu___18 =
                                                             let uu___19 =
                                                               pp uu___3 w in
                                                             FStar_Tactics_Effect.tac_bind
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
                                                                    pp uu___4
                                                                    v in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Slash_Hat
                                                                    FStarC_Pprint.comma
                                                                    uu___23)) in
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
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___20
                                                                    uu___22))))
                                                                    uu___20) in
                                                           FStar_Tactics_Effect.tac_bind
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
                                                                uu___18)
                                                             (fun uu___19 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun
                                                                    uu___20
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Slash_Hat
                                                                    FStarC_Pprint.comma
                                                                    uu___19)) in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (115)))))
                                                              (Obj.magic
                                                                 uu___17)
                                                              (fun uu___18 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___19
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___16
                                                                    uu___18))))
                                                        uu___16) in
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
                                                 (Obj.magic uu___14)
                                                 (fun uu___15 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___16 ->
                                                         FStarC_Pprint.op_Hat_Slash_Hat
                                                           FStarC_Pprint.comma
                                                           uu___15)) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.PP.fst"
                                                           (Prims.of_int (123))
                                                           (Prims.of_int (65))
                                                           (Prims.of_int (123))
                                                           (Prims.of_int (115)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.PP.fst"
                                                           (Prims.of_int (123))
                                                           (Prims.of_int (57))
                                                           (Prims.of_int (123))
                                                           (Prims.of_int (115)))))
                                                  (Obj.magic uu___13)
                                                  (fun uu___14 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___15 ->
                                                          FStarC_Pprint.op_Hat_Hat
                                                            uu___12 uu___14))))
                                            uu___12) in
                                   FStar_Tactics_Effect.tac_bind
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
                                     (Obj.magic uu___10)
                                     (fun uu___11 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___12 ->
                                             FStarC_Pprint.op_Hat_Slash_Hat
                                               FStarC_Pprint.comma uu___11)) in
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
                                      (Obj.magic uu___9)
                                      (fun uu___10 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___11 ->
                                              FStarC_Pprint.op_Hat_Hat uu___8
                                                uu___10)))) uu___8) in
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
                         (Obj.magic uu___6)
                         (fun uu___7 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___8 -> FStarC_Pprint.parens uu___7)))
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
                         let uu___7 =
                           let uu___8 = pp uu___ x in
                           FStar_Tactics_Effect.tac_bind
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
                             (Obj.magic uu___8)
                             (fun uu___9 ->
                                (fun uu___9 ->
                                   let uu___10 =
                                     let uu___11 =
                                       let uu___12 = pp uu___1 y in
                                       FStar_Tactics_Effect.tac_bind
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
                                         (Obj.magic uu___12)
                                         (fun uu___13 ->
                                            (fun uu___13 ->
                                               let uu___14 =
                                                 let uu___15 =
                                                   let uu___16 = pp uu___2 z in
                                                   FStar_Tactics_Effect.tac_bind
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
                                                     (Obj.magic uu___16)
                                                     (fun uu___17 ->
                                                        (fun uu___17 ->
                                                           let uu___18 =
                                                             let uu___19 =
                                                               let uu___20 =
                                                                 pp uu___3 w in
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (100)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (136)))))
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
                                                                    pp uu___4
                                                                    v in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    pp uu___5
                                                                    u in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Slash_Hat
                                                                    FStarC_Pprint.comma
                                                                    uu___28)) in
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
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___25
                                                                    uu___27))))
                                                                    uu___25) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Slash_Hat
                                                                    FStarC_Pprint.comma
                                                                    uu___24)) in
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
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___21
                                                                    uu___23))))
                                                                    uu___21) in
                                                             FStar_Tactics_Effect.tac_bind
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
                                                                  uu___19)
                                                               (fun uu___20
                                                                  ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___21
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Slash_Hat
                                                                    FStarC_Pprint.comma
                                                                    uu___20)) in
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
                                                                   uu___18)
                                                                (fun uu___19
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___17
                                                                    uu___19))))
                                                          uu___17) in
                                                 FStar_Tactics_Effect.tac_bind
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
                                                   (Obj.magic uu___15)
                                                   (fun uu___16 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___17 ->
                                                           FStarC_Pprint.op_Hat_Slash_Hat
                                                             FStarC_Pprint.comma
                                                             uu___16)) in
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
                                                    (Obj.magic uu___14)
                                                    (fun uu___15 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___16 ->
                                                            FStarC_Pprint.op_Hat_Hat
                                                              uu___13 uu___15))))
                                              uu___13) in
                                     FStar_Tactics_Effect.tac_bind
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
                                       (Obj.magic uu___11)
                                       (fun uu___12 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___13 ->
                                               FStarC_Pprint.op_Hat_Slash_Hat
                                                 FStarC_Pprint.comma uu___12)) in
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
                                        (Obj.magic uu___10)
                                        (fun uu___11 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___12 ->
                                                FStarC_Pprint.op_Hat_Hat
                                                  uu___9 uu___11)))) uu___9) in
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
                           (Obj.magic uu___7)
                           (fun uu___8 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___9 -> FStarC_Pprint.parens uu___8)))
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
                           let uu___8 =
                             let uu___9 = pp uu___ x in
                             FStar_Tactics_Effect.tac_bind
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
                               (Obj.magic uu___9)
                               (fun uu___10 ->
                                  (fun uu___10 ->
                                     let uu___11 =
                                       let uu___12 =
                                         let uu___13 = pp uu___1 y in
                                         FStar_Tactics_Effect.tac_bind
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
                                           (Obj.magic uu___13)
                                           (fun uu___14 ->
                                              (fun uu___14 ->
                                                 let uu___15 =
                                                   let uu___16 =
                                                     let uu___17 =
                                                       pp uu___2 z in
                                                     FStar_Tactics_Effect.tac_bind
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
                                                       (Obj.magic uu___17)
                                                       (fun uu___18 ->
                                                          (fun uu___18 ->
                                                             let uu___19 =
                                                               let uu___20 =
                                                                 let uu___21
                                                                   =
                                                                   pp uu___3
                                                                    w in
                                                                 FStar_Tactics_Effect.tac_bind
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
                                                                    pp uu___4
                                                                    v in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    pp uu___5
                                                                    u in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    pp uu___6
                                                                    t in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Slash_Hat
                                                                    FStarC_Pprint.comma
                                                                    uu___33)) in
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
                                                                    uu___31)
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___30
                                                                    uu___32))))
                                                                    uu___30) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Slash_Hat
                                                                    FStarC_Pprint.comma
                                                                    uu___29)) in
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
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___26
                                                                    uu___28))))
                                                                    uu___26) in
                                                                    FStar_Tactics_Effect.tac_bind
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
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Slash_Hat
                                                                    FStarC_Pprint.comma
                                                                    uu___25)) in
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
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___22
                                                                    uu___24))))
                                                                    uu___22) in
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.PP.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (157)))))
                                                                 (Obj.magic
                                                                    uu___20)
                                                                 (fun uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Slash_Hat
                                                                    FStarC_Pprint.comma
                                                                    uu___21)) in
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
                                                                    uu___19)
                                                                  (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___18
                                                                    uu___20))))
                                                            uu___18) in
                                                   FStar_Tactics_Effect.tac_bind
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
                                                     (Obj.magic uu___16)
                                                     (fun uu___17 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___18 ->
                                                             FStarC_Pprint.op_Hat_Slash_Hat
                                                               FStarC_Pprint.comma
                                                               uu___17)) in
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
                                                      (Obj.magic uu___15)
                                                      (fun uu___16 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___17 ->
                                                              FStarC_Pprint.op_Hat_Hat
                                                                uu___14
                                                                uu___16))))
                                                uu___14) in
                                       FStar_Tactics_Effect.tac_bind
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
                                         (Obj.magic uu___12)
                                         (fun uu___13 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___14 ->
                                                 FStarC_Pprint.op_Hat_Slash_Hat
                                                   FStarC_Pprint.comma uu___13)) in
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
                                          (Obj.magic uu___11)
                                          (fun uu___12 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___13 ->
                                                  FStarC_Pprint.op_Hat_Hat
                                                    uu___10 uu___12))))
                                    uu___10) in
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
                             (Obj.magic uu___8)
                             (fun uu___9 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___10 -> FStarC_Pprint.parens uu___9)))
                }